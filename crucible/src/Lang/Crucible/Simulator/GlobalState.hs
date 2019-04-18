{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Lang.Crucible.Simulator.GlobalState
  ( SymGlobalState
  , emptyGlobals
  , insertGlobal
  , lookupGlobal
  , insertRef
  , lookupRef
  , dropRef
  , updateRef
  , globalPushBranch
  , globalAbortBranch
  , globalMuxFn
  ) where

import           Data.Kind
import qualified Data.Parameterized.Map as MapF
import           Data.Parameterized.TraversableF

import           What4.Interface
import           What4.Partial
import           What4.ProgramLoc

import           Lang.Crucible.CFG.Core
import           Lang.Crucible.FunctionHandle
import           Lang.Crucible.Simulator.Intrinsics
import           Lang.Crucible.Simulator.RegMap
import           Lang.Crucible.Backend
import           Lang.Crucible.Panic(panic)

data GlobalEntry (sym :: Type) (tp :: CrucibleType)
  = GlobalEntry { globalEntryPending :: !Int, globalEntryValue :: !(RegValue sym tp) }

-- The Int records the number of pending branches that were in the
-- global state when the cell was last updated.
data RefCellContents (sym :: Type) (tp :: CrucibleType)
  = RefCellContents !Int !(Pred sym) !(RegValue sym tp)

------------------------------------------------------------------------
-- SymGlobalState

-- | Maps from global variables and global references to their values.
data SymGlobalState (sym :: Type) =
  GlobalState
  { _globalPendingBranches :: Int
    -- ^ The integer value is the number of symbolic branches
    -- currently pending. We use this primarily as a sanity check to
    -- help find bugs where we fail to match up calls to
    -- 'globalPushBranch' with 'globalAbortBranch'/'globalMuxFn'.
  , globalMap             :: MapF.MapF GlobalVar (GlobalEntry sym)
  , globalReferenceMap    :: MapF.MapF RefCell (RefCellContents sym)
  }

-- | The empty set of global variable bindings.
emptyGlobals :: SymGlobalState sym
emptyGlobals = GlobalState 0 MapF.empty MapF.empty

-- | Look up a global in the state.
lookupGlobal :: GlobalVar tp -> SymGlobalState sym -> Maybe (RegValue sym tp)
lookupGlobal g gst = globalEntryValue <$> MapF.lookup g (globalMap gst)

-- | Set the value of a global in the state.
insertGlobal :: GlobalVar tp
             -> RegValue sym tp
             -> SymGlobalState sym
             -> SymGlobalState sym
insertGlobal g v (GlobalState d vars refs) =
  GlobalState d (MapF.insert g (GlobalEntry d v) vars) refs

-- | Look up the value of a reference cell in the state.
lookupRef :: RefCell tp -> SymGlobalState sym -> PartExpr (Pred sym) (RegValue sym tp)
lookupRef r gst =
  maybe Unassigned (\(RefCellContents _ p x) -> PE p x) $ MapF.lookup r (globalReferenceMap gst)

-- | Set the value of a reference cell in the state.
insertRef :: IsExprBuilder sym
          => sym
          -> RefCell tp
          -> RegValue sym tp
          -> SymGlobalState sym
          -> SymGlobalState sym
insertRef sym r v (GlobalState d vars refs) =
  GlobalState d vars (MapF.insert r x refs)
  where x = RefCellContents d (truePred sym) v

-- | Write a partial value to a reference cell in the state.
updateRef ::
  IsExprBuilder sym =>
  RefCell tp ->
  PartExpr (Pred sym) (RegValue sym tp) ->
  SymGlobalState sym ->
  SymGlobalState sym
updateRef r pe (GlobalState d vars refs) =
  case pe of
    Unassigned -> GlobalState d vars (MapF.delete r refs)
    PE p x -> GlobalState d vars (MapF.insert r (RefCellContents d p x) refs)

-- | Reset a reference cell to the uninitialized state. @'dropRef' r@ is
-- equivalent to @'updateRef' r 'Unassigned'@.
dropRef :: RefCell tp -> SymGlobalState sym -> SymGlobalState sym
dropRef r (GlobalState d vars refs) =
  GlobalState d vars (MapF.delete r refs)

-- | Test whether this type could be an intrinsic type, which must be
-- notified of branch pushes and aborts.
needsNotification :: TypeRepr tp -> Bool
needsNotification tr =
  case tr of
    IntrinsicRepr{} -> True
    AnyRepr -> True
    _ -> False

globalPushBranch ::
  forall sym .
  IsSymInterface sym =>
  sym ->
  IntrinsicTypes sym ->
  SymGlobalState sym ->
  IO (SymGlobalState sym)
globalPushBranch sym iTypes (GlobalState d vars refs) =
  do let d' = d + 1
     vars' <- MapF.traverseWithKey
              (\v x@(GlobalEntry _ e) ->
                if needsNotification (globalType v)
                then GlobalEntry d' <$> pushBranchForType sym iTypes (globalType v) e
                else return x)
              vars
     refs' <- MapF.traverseWithKey
              (\r x@(RefCellContents _ p e) ->
                if needsNotification (refType r)
                then RefCellContents d' p <$> pushBranchForType sym iTypes (refType r) e
                else return x)
              refs

     --loc <- getCurrentProgramLoc sym
     --putStrLn $ unwords ["PUSH BRANCH:", show d, show $ plSourceLoc loc]
     return (GlobalState d' vars' refs')

globalAbortBranch ::
  forall sym .
  IsSymInterface sym =>
  sym ->
  IntrinsicTypes sym ->
  SymGlobalState sym ->
  IO (SymGlobalState sym)
globalAbortBranch sym iTypes (GlobalState d vars refs)
  | d > 0 =
    do let d' = d - 1
       vars' <- MapF.traverseWithKey
                (\v (GlobalEntry i e) ->
                  GlobalEntry (max i d') <$> abortBranchForType sym iTypes (globalType v) e)
                vars
       refs' <- MapF.traverseWithKey
                (\r (RefCellContents i p e) ->
                  RefCellContents (max i d') p <$> abortBranchForType sym iTypes (refType r) e)
                refs

       --loc <- getCurrentProgramLoc sym
       --putStrLn $ unwords ["ABORT BRANCH:", show (d-1), show $ plSourceLoc loc]
       return (GlobalState d' vars' refs')

  | otherwise =
    do loc <- getCurrentProgramLoc sym
       panic "GlobalState.globalAbortBranch"
             [ "Attempting to commit global changes at incorrect branch depth"
             , "*** Depth:    " ++ show d
             , "*** Location: " ++ show (plSourceLoc loc)
             ]

globalMuxFn :: forall sym
             . IsSymInterface sym
             => sym
             -> IntrinsicTypes sym
             -> MuxFn (Pred sym) (SymGlobalState sym)
globalMuxFn sym iteFns c (GlobalState d1 vars1 refs1) (GlobalState d2 vars2 refs2)
  | d1 > 0 && d1 == d2 =
    GlobalState d' <$> MapF.mergeWithKeyM muxEntry checkNullMap checkNullMap vars1 vars2
                   <*> MapF.mergeWithKeyM muxRef refLeft refRight refs1 refs2
  where
    d' :: Int
    d' = d1 - 1

    muxEntry ::
      GlobalVar tp ->
      GlobalEntry sym tp ->
      GlobalEntry sym tp ->
      IO (Maybe (GlobalEntry sym tp))
    muxEntry g x@(GlobalEntry i u) (GlobalEntry j v)
      | i < d1 && j < d2 = return (Just x) -- unmodified since last branch, so entries should be equal
      | otherwise =
        Just . GlobalEntry d' <$> muxRegForType sym iteFns (globalType g) c u v

    muxRef ::
      RefCell tp ->
      RefCellContents sym tp ->
      RefCellContents sym tp ->
      IO (Maybe (RefCellContents sym tp))
    muxRef r x@(RefCellContents i pu u) (RefCellContents j pv v)
      | i < d1 && j < d2 = return (Just x) -- unmodified since last branch, so entries should be equal
      | otherwise =
        do uv <- muxRegForType sym iteFns (refType r) c u v
           p <- itePred sym c pu pv
           return $ Just (RefCellContents d' p uv)

    refLeft :: MapF.MapF RefCell (RefCellContents sym) -> IO (MapF.MapF RefCell (RefCellContents sym))
    refLeft m = traverseF f m
      where f :: RefCellContents sym tp -> IO (RefCellContents sym tp)
            f (RefCellContents _ p z) =
              do p' <- andPred sym c p
                 return $ RefCellContents d' p' z

    refRight :: MapF.MapF RefCell (RefCellContents sym) -> IO (MapF.MapF RefCell (RefCellContents sym))
    refRight m = do cnot <- notPred sym c; traverseF (f cnot) m
      where f :: Pred sym -> RefCellContents sym tp -> IO (RefCellContents sym tp)
            f cnot (RefCellContents _ p z) =
              do p' <- andPred sym cnot p
                 return $ RefCellContents d' p' z

    checkNullMap :: MapF.MapF GlobalVar (GlobalEntry sym) -> IO (MapF.MapF GlobalVar (GlobalEntry sym))
    checkNullMap m
      | MapF.null m = return m
      | otherwise =
        panic "GlobalState.globalMuxFn"
              [ "Different global variables in each branch." ]

globalMuxFn sym _ _ (GlobalState d1 _ _) (GlobalState d2 _ _) =
  do loc <- getCurrentProgramLoc sym
     panic "GlobalState.globalMuxFn"
           [ "Attempting to merge global states of incorrect branch depths:"
           , " *** Depth 1:  " ++ show d1
           , " *** Depth 2:  " ++ show d2
           , " *** Location: " ++ show (plSourceLoc loc)
           ]
