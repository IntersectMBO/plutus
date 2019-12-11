-- | The CEK machine.
-- Rules are the same as for the CK machine from "Language.PlutusCore.Evaluation.CkMachine",
-- except we do not use substitution and use environments instead.
-- The CEK machine relies on variables having non-equal 'Unique's whenever they have non-equal
-- string names. I.e. 'Unique's are used instead of string names. This is for efficiency reasons.
-- The type checker pass is a prerequisite.
-- Feeding ill-typed terms to the CEK machine will likely result in a 'MachineException'.
-- The CEK machine generates booleans along the way which might contain globally non-unique 'Unique's.
-- This is not a problem as the CEK machines handles name capture by design.
-- Dynamic extensions to the set of built-ins are allowed.
-- In case an unknown dynamic built-in is encountered, an 'UnknownDynamicBuiltinNameError' is returned
-- (wrapped in 'OtherMachineError').

{-# LANGUAGE TemplateHaskell #-}

module Language.PlutusCore.Merkle.Evaluation.CekMarker
    ( CekMachineException
    , EvaluationResult (..)
    , EvaluationResultDef2
    , evaluateCek
    , unsafeEvaluateCek
--    , readKnownCek
    , runCek
    , unsafeRunCek
    ) where

import           Language.PlutusCore                                    hiding (EvaluationResultDef)
import           Language.PlutusCore.Constant
import           Language.PlutusCore.Merkle.Convert
import           Language.PlutusCore.Merkle.Evaluation.MachineException
import           Language.PlutusCore.Name
import           Language.PlutusCore.View

import           PlutusPrelude                                          hiding (hoist)

import           Control.Lens.TH                                        (makeLenses)
import           Control.Monad.Except
import           Control.Monad.Reader
import           Control.Monad.State
import qualified Data.Map                                               as Map
import qualified Data.Set                                               as Set


type Numbered f = f TyName Name Integer

type NodeIDs = Set.Set Integer

type EvaluationResultDef2 = EvaluationResult (Numbered Term, NodeIDs)

type EvaluationResultDef ann = EvaluationResult (Term TyName Name ann)
type Evaluator f m ann = DynamicBuiltinNameMeanings -> f TyName Name ann -> m (EvaluationResultDef ann)

-- | The monad the CEK machine runs in.
type CekM = ReaderT CekEnv (ExceptT CekMachineException (State NodeIDs))

{-
fixEvalResult :: EvaluationResultDef -> EvaluationResultDef2
fixEvalResult (EvaluationSuccess t) = EvaluationSuccess (fakeIDs t, Set.empty)
fixEvalResult EvaluationFailure     = EvaluationFailure

fixEvalResult2 :: Either a EvaluationResultDef -> Either a EvaluationResultDef2
fixEvalResult2 (Left x)  = Left x
fixEvalResult2 (Right r) = Right (fixEvalResult r)
-}

unann :: Functor f => f a -> f()
unann = fmap (\_ -> ())
-- Remove annotations.  We require this because the builtin
-- application mechanism expects terms annotated with ().

fakeID :: Integer
fakeID = -1

fakeIDs :: Functor f => f () -> f Integer
fakeIDs = fmap (\() -> fakeID)
{- Again with the builtins.  Builtin application gives us back something
   of type Plain Term, but we expect a Numbered Term.  This is
   problematic: we may give a builtin a numbered term and it might
   return some completely new term that we haven't seen before (a
   Church boolean, for example), or it might return a term
   manufactured from the ones supplied as arguments.  We can't
   possibly know whether it does the former or the latter.

The best solution to this is probably to mark every node in a term
   as being used when we supply it as an argument to a builtin.  We
   can't tell what the builtin's going to do with the term, so it's
   not safe to Merklise any part of it away.
-}

-- Insert all of the node IDs in a term into the set of used IDs. This
-- may be extravagant because it will insert IDs of names and other
-- things that we don't care about. Think about this again.
markAll :: NodeIDs -> Numbered Term -> NodeIDs
markAll = Prelude.foldr Set.insert

-- | The CEK machine-specific 'MachineException'.
type CekMachineException = MachineException UnknownDynamicBuiltinNameError

-- | A 'Value' packed together with the environment it's defined in.
data Closure = Closure
    { _closureVarEnv :: VarEnv
    , _closureValue  :: Numbered Value
    }

-- | Variable environments used by the CEK machine.
-- Each row is a mapping from the 'Unique' representing a variable to a 'Closure'.
type VarEnv = UniqueMap TermUnique Closure

-- | The environment the CEK machine runs in.
data CekEnv = CekEnv
    { _cekEnvMeans  :: DynamicBuiltinNameMeanings
    , _cekEnvVarEnv :: VarEnv
    }


data Frame
    = FrameApplyFun VarEnv (Numbered Value)        -- ^ @[V _]@
    | FrameApplyArg VarEnv (Numbered Term)         -- ^ @[_ N]@
    | FrameTyInstArg (Type TyName Integer)         -- ^ @{_ A}@
    | FrameUnwrap                                  -- ^ @(unwrap _)@
    | FrameIWrap Integer (Type TyName Integer) (Type TyName Integer)  -- ^ @(iwrap A B _)@

type Context = [Frame]

makeLenses ''CekEnv

runCekM :: CekEnv -> CekM a -> Either CekMachineException a
runCekM = flip runReaderT

-- | Get the current 'VarEnv'.
getVarEnv :: CekM VarEnv
getVarEnv = asks _cekEnvVarEnv

-- | Set a new 'VarEnv' and proceed.
withVarEnv :: VarEnv -> CekM a -> CekM a
withVarEnv = local . set cekEnvVarEnv

-- | Extend an environment with a variable name, the value the variable stands for
-- and the environment the value is defined in.
extendVarEnv :: Name Integer -> Numbered Value -> VarEnv -> VarEnv -> VarEnv
extendVarEnv argName arg argVarEnv = insertByName argName $ Closure argVarEnv arg

-- | Look up a variable name in the environment.
lookupVarName :: Name Integer -> CekM Closure
lookupVarName varName = do
    varEnv <- getVarEnv
    case lookupName varName varEnv of
        Nothing   -> throwError $ MachineException OpenTermEvaluatedMachineError (Var () (unann varName))
        Just clos -> pure clos

-- | Look up a 'DynamicBuiltinName' in the environment.
lookupDynamicBuiltinName :: DynamicBuiltinName -> CekM DynamicBuiltinNameMeaning
lookupDynamicBuiltinName dynName = do
    DynamicBuiltinNameMeanings means <- asks _cekEnvMeans
    case Map.lookup dynName means of
        Nothing   -> throwError $ MachineException err term where
            err  = OtherMachineError $ UnknownDynamicBuiltinNameErrorE dynName
            term = Builtin () $ DynBuiltinName () dynName
        Just mean -> pure mean

-- We need a set of node ids in the state, and whenever
-- we evaluate a node we add its id to the set.  At the end,
-- we take the set of all of the nodes which were used and traverse
-- the AST.  When we meet an unused node, we Merklise it away.
-- This gives us something of the type
-- Term tn n Int -> Set (NodeId) -> MerklisedTerm tn n ()

-- | The computing part of the CEK machine.
-- Either
-- 1. adds a frame to the context and calls 'computeCek' ('TyInst', 'Apply', 'IWrap', 'Unwrap')
-- 2. calls 'returnCek' on values ('TyAbs', 'LamAbs', 'Constant')
-- 3. returns 'EvaluationFailure' ('Error')
-- 4. looks up a variable in the environment and calls 'returnCek' ('Var')
computeCek :: Context -> NodeIDs -> Numbered Term -> CekM EvaluationResultDef2
computeCek con usedNodes thisTerm =
    let usedNodes' = Set.insert (termLoc thisTerm) usedNodes
    in case thisTerm of
         TyInst _ body ty       -> computeCek (FrameTyInstArg ty : con) usedNodes' body
         Apply _ fun arg        ->
             do
               varEnv <- getVarEnv
               computeCek (FrameApplyArg varEnv arg : con) usedNodes' fun
         IWrap ann pat arg term -> computeCek (FrameIWrap ann pat arg : con) usedNodes' term
         Unwrap _ term          -> computeCek (FrameUnwrap : con) usedNodes' term
         tyAbs@TyAbs{}          -> returnCek con usedNodes' tyAbs
         lamAbs@LamAbs{}        -> returnCek con usedNodes' lamAbs
         constant@Constant{}    -> returnCek con usedNodes' constant
         bi@Builtin{}           -> returnCek con usedNodes' bi
         Error{}                -> pure EvaluationFailure
         Var _ varName          ->
             do
               Closure newVarEnv term <- lookupVarName varName
               withVarEnv newVarEnv $ returnCek con usedNodes' term


-- | The returning part of the CEK machine.
-- Returns 'EvaluationSuccess' in case the context is empty, otherwise pops up one frame
-- from the context and either
-- 1. performs reduction and calls 'computeCek' ('FrameTyInstArg', 'FrameApplyFun', 'FrameUnwrap')
-- 2. performs a constant application and calls 'returnCek' ('FrameTyInstArg', 'FrameApplyFun')
-- 3. puts 'FrameApplyFun' on top of the context and proceeds with the argument from 'FrameApplyArg'
-- 4. grows the resulting term ('FrameWrap')
returnCek :: Context -> NodeIDs -> Numbered Value -> CekM EvaluationResultDef2
returnCek con0 usedNodes val =
    case con0 of
      [] -> pure $ EvaluationSuccess (val, markAll usedNodes val)
      -- We don't know what'll be done with the result, so we'd better
      -- be conservative and not Merklise any of it away
      FrameTyInstArg ty : con -> instantiateEvaluate con usedNodes ty val
      FrameApplyArg argVarEnv arg : con -> do
               funVarEnv <- getVarEnv
               withVarEnv argVarEnv $ computeCek (FrameApplyFun funVarEnv val : con) usedNodes arg
      FrameApplyFun funVarEnv fun : con -> do
               argVarEnv <- getVarEnv
               applyEvaluate funVarEnv argVarEnv con usedNodes fun val
      FrameIWrap ann pat arg : con -> returnCek con usedNodes (IWrap ann pat arg val)
      FrameUnwrap : con ->
          case val of
            IWrap _ _ _ term -> returnCek con usedNodes term
            term             -> throwError $ MachineException NonWrapUnwrappedMachineError (unann term)

-- TODO: Check that we never need to update the used nodes aboves

-- | Instantiate a term with a type and proceed.
-- In case of 'TyAbs' just ignore the type. Otherwise check if the term is an
-- iterated application of a 'BuiltinName' to a list of 'Value's and, if succesful,
-- apply the term to the type via 'TyInst'.
instantiateEvaluate :: Context -> NodeIDs -> Type TyName Integer -> Numbered Term -> CekM EvaluationResultDef2
instantiateEvaluate con usedNodes  _  (TyAbs _ _ _ body)= computeCek con usedNodes body
instantiateEvaluate con usedNodes ty fun
    | isJust $ termAsPrimIterApp fun = returnCek con usedNodes (TyInst fakeID fun ty)
    | otherwise                      =
        throwError $ MachineException NonPrimitiveInstantiationMachineError (unann fun)

-- | Apply a function to an argument and proceed.
-- If the function is a 'LamAbs', then extend the current environment with a new variable and proceed.
-- If the function is not a 'LamAbs', then 'Apply' it to the argument and view this
-- as an iterated application of a 'BuiltinName' to a list of 'Value's.
-- If succesful, proceed with either this same term or with the result of the computation
-- depending on whether 'BuiltinName' is saturated or not.
applyEvaluate
    :: VarEnv -> VarEnv -> Context -> NodeIDs -> Numbered Value -> Numbered Value -> CekM EvaluationResultDef2
applyEvaluate funVarEnv argVarEnv con usedNodes (LamAbs _ name _ body) arg =
    withVarEnv (extendVarEnv name arg argVarEnv funVarEnv) $ computeCek con usedNodes body
applyEvaluate funVarEnv _         con usedNodes fun                    arg =
    let term = Apply 0 fun arg in  -- 0????
        case termAsPrimIterApp term of
            Nothing                       ->
                throwError $ MachineException NonPrimitiveApplicationMachineError (unann term)
            Just (IterApp headName spine) -> do
                constAppResult <- applyStagedBuiltinName headName spine
                withVarEnv funVarEnv $ case constAppResult of
                    ConstAppSuccess res -> computeCek con usedNodes (fakeIDs res)
                    ConstAppFailure     -> pure EvaluationFailure
                    ConstAppStuck       -> returnCek con usedNodes term
                    ConstAppError   err ->
                        throwError $ MachineException (ConstAppMachineError err) (unann term)


evaluateInCekM :: EvaluateConstApp (ExceptT CekMachineException (State NodeIDs)) a -> CekM (ConstAppResult a)
-- evaluateInCekM :: EvaluateConstApp (Either CekMachineException) a -> CekM (ConstAppResult a)
evaluateInCekM a = undefined
{-    ReaderT $ \cekEnv ->
        let eval means' = evaluateCekIn $ cekEnv & cekEnvMeans %~ mappend means'
            in runEvaluateConstApp eval a
-}
-- ^^^ THIS IS BROKEN ^^^ --

-- runEvaluateConstApp :: Evaluator Term m -> EvaluateConstApp m a -> m (ConstAppResult a)
-- runEvaluateConstApp eval = unInnerT . runEvaluateT eval
-- ^ In Apply.hs


applyStagedBuiltinName :: StagedBuiltinName -> [Numbered Value] -> CekM ConstAppResultDef
applyStagedBuiltinName (DynamicStagedBuiltinName name) args = do
    DynamicBuiltinNameMeaning sch x <- lookupDynamicBuiltinName name
    evaluateInCekM $ applyTypeSchemed sch x (map unann args)
applyStagedBuiltinName (StaticStagedBuiltinName  name) args =
    evaluateInCekM $ applyBuiltinName name (map unann args)
                   -- FIXME: Do we have to mark the args as being
                   -- used? If so, we have to do it deeply because we
                   -- can't know what the builtin will do with them.

-- | Evaluate a term in an environment using the CEK machine.
evaluateCekIn
    :: CekEnv -> Numbered Term -> Either CekMachineException EvaluationResultDef2
evaluateCekIn cekEnv = (runCekM cekEnv) . (computeCek [] Set.empty)

-- | Evaluate a term using the CEK machine.
evaluateCek
    :: DynamicBuiltinNameMeanings -> Numbered Term -> Either CekMachineException EvaluationResultDef2
evaluateCek means term = evaluateCekIn (CekEnv means mempty) term

-- | Evaluate a term using the CEK machine. May throw a 'CekMachineException'.
unsafeEvaluateCek :: DynamicBuiltinNameMeanings -> Numbered Term -> EvaluationResultDef2
unsafeEvaluateCek means term = either throw id $ (evaluateCek means term)

{- Deleted readKnownCek -}

-- | Run a program using the CEK machine.
-- Calls 'evaluateCekCatch' under the hood.
runCek :: DynamicBuiltinNameMeanings -> Numbered Program -> Either CekMachineException EvaluationResultDef2
runCek means (Program _ _ term) = evaluateCek means term

-- | Run a program using the CEK machine. May throw a 'CekMachineException'.
-- Calls 'evaluateCek' under the hood.
unsafeRunCek :: DynamicBuiltinNameMeanings -> Numbered Program -> EvaluationResultDef2
unsafeRunCek means (Program _ _ term) = unsafeEvaluateCek means term
