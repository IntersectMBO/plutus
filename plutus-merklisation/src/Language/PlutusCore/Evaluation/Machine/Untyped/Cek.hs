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

module Language.PlutusCore.Evaluation.Machine.Untyped.Cek
    ( CekMachineException
    , EvaluationResult (..)
    , EvaluationResultDef
    , evaluateCek
    , unsafeEvaluateCek
    , readKnownCek
    , runCek
    , unsafeRunCek
    ) where

import qualified Language.PlutusCore                                             as PLC
import           Language.PlutusCore.Erasure.Untyped.Constant
import           Language.PlutusCore.Erasure.Untyped.Constant.Typed
import           Language.PlutusCore.Erasure.Untyped.Evaluation.MachineException
import           Language.PlutusCore.Erasure.Untyped.Evaluation.Result
import           Language.PlutusCore.Erasure.Untyped.Term
import           Language.PlutusCore.Erasure.Untyped.View
import           Language.PlutusCore.Name

import           PlutusPrelude

import           Control.Lens.TH                                                 (makeLenses)
import           Control.Monad.Except
import           Control.Monad.Reader
import qualified Data.Map                                                        as Map

type Plain f = f Name ()

-- | The CEK machine-specific 'MachineException'.
type CekMachineException =
    MachineException PLC.UnknownDynamicBuiltinNameError

-- | A 'Value' packed together with the environment it's defined in.
data Closure = Closure
    { _closureVarEnv :: VarEnv
    , _closureValue  :: Plain Value
    }

-- | Variable environments used by the CEK machine.
-- Each row is a mapping from the 'Unique' representing a variable to a 'Closure'.
type VarEnv = UniqueMap TermUnique Closure

-- | The environment the CEK machine runs in.
data CekEnv = CekEnv
    { _cekEnvMeans  :: DynamicBuiltinNameMeanings
    , _cekEnvVarEnv :: VarEnv
    }

-- | The monad the CEK machine runs in.
type CekM a = ReaderT CekEnv (Either CekMachineException) a

data Frame
    = FrameApplyFun VarEnv (Plain Value)               -- ^ @[V _]@
    | FrameApplyArg VarEnv (Plain Term)                -- ^ @[_ N]@

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
extendVarEnv :: Name () -> Plain Value -> VarEnv -> VarEnv -> VarEnv
extendVarEnv argName arg argVarEnv = insertByName argName $ Closure argVarEnv arg

-- | Look up a variable name in the environment.
lookupVarName :: Name () -> CekM Closure
lookupVarName varName = do
    varEnv <- getVarEnv
    case lookupName varName varEnv of
        Nothing   -> throwError $ MachineException OpenTermEvaluatedMachineError (Var () varName)
        Just clos -> pure clos

-- | Look up a 'DynamicBuiltinName' in the environment.
lookupDynamicBuiltinName :: PLC.DynamicBuiltinName -> CekM DynamicBuiltinNameMeaning
lookupDynamicBuiltinName dynName = do
    DynamicBuiltinNameMeanings means <- asks _cekEnvMeans
    case Map.lookup dynName means of
        Nothing   -> throwError $ MachineException err term where
            err  = OtherMachineError $ PLC.UnknownDynamicBuiltinNameErrorE dynName
            term = Builtin () $ DynBuiltinName () dynName
        Just mean -> pure mean

-- | The computing part of the CEK machine.
-- Either
-- 1. adds a frame to the context and calls 'computeCek' ('TyInst', 'Apply', 'IWrap', 'Unwrap')
-- 2. calls 'returnCek' on values ('TyAbs', 'LamAbs', 'Constant')
-- 3. returns 'EvaluationFailure' ('Error')
-- 4. looks up a variable in the environment and calls 'returnCek' ('Var')
computeCek :: Context -> Plain Term -> CekM EvaluationResultDef
computeCek con (Apply _ fun arg)        = do
    varEnv <- getVarEnv
    computeCek (FrameApplyArg varEnv arg : con) fun
computeCek con lamAbs@LamAbs{}          = returnCek con lamAbs
computeCek con constant@Constant{}      = returnCek con constant
computeCek con bi@Builtin{}             = returnCek con bi
computeCek _   Error{}                  = pure EvaluationFailure
computeCek _   Prune{}                  = error "Attempting to compute Merklised term"
-- ^ FIXME: Wasted a long time trying to do this properly then gave up
computeCek con (Var _ varName)          = do
    Closure newVarEnv term <- lookupVarName varName
    withVarEnv newVarEnv $ returnCek con term

-- | The returning part of the CEK machine.
-- Returns 'EvaluationSuccess' in case the context is empty, otherwise pops up one frame
-- from the context and either
-- 1. performs reduction and calls 'computeCek' ('FrameTyInstArg', 'FrameApplyFun', 'FrameUnwrap')
-- 2. performs a constant application and calls 'returnCek' ('FrameTyInstArg', 'FrameApplyFun')
-- 3. puts 'FrameApplyFun' on top of the context and proceeds with the argument from 'FrameApplyArg'
-- 4. grows the resulting term ('FrameWrap')
returnCek :: Context -> Plain Value -> CekM EvaluationResultDef
returnCek []                                  res = pure $ EvaluationSuccess res
returnCek (FrameApplyArg argVarEnv arg : con) fun = do
    funVarEnv <- getVarEnv
    withVarEnv argVarEnv $ computeCek (FrameApplyFun funVarEnv fun : con) arg
returnCek (FrameApplyFun funVarEnv fun : con) arg = do
    argVarEnv <- getVarEnv
    applyEvaluate funVarEnv argVarEnv con fun arg

-- | Apply a function to an argument and proceed.
-- If the function is a 'LamAbs', then extend the current environment with a new variable and proceed.
-- If the function is not a 'LamAbs', then 'Apply' it to the argument and view this
-- as an iterated application of a 'BuiltinName' to a list of 'Value's.
-- If succesful, proceed with either this same term or with the result of the computation
-- depending on whether 'BuiltinName' is saturated or not.
applyEvaluate
    :: VarEnv -> VarEnv -> Context -> Plain Value -> Plain Value -> CekM EvaluationResultDef
applyEvaluate funVarEnv argVarEnv con (LamAbs _ name body) arg =
    withVarEnv (extendVarEnv name arg argVarEnv funVarEnv) $ computeCek con body
applyEvaluate funVarEnv _         con fun                    arg =
    let term = Apply () fun arg in
        case termAsPrimIterApp term of
            Nothing                       ->
                throwError $ MachineException NonPrimitiveApplicationMachineError term
            Just (IterApp headName spine) -> do
                constAppResult <- applyStagedBuiltinName headName spine
                withVarEnv funVarEnv $ case constAppResult of
                    ConstAppSuccess res -> computeCek con res
                    ConstAppFailure     -> pure EvaluationFailure
                    ConstAppStuck       -> returnCek con term
                    ConstAppError   err ->
                        throwError $ MachineException (ConstAppMachineError err) term

evaluateInCekM :: EvaluateConstApp (Either CekMachineException) a -> CekM (ConstAppResult a)
evaluateInCekM a =
    ReaderT $ \cekEnv ->
        let eval means' = evaluateCekIn $ cekEnv & cekEnvMeans %~ mappend means'
            in runEvaluateConstApp eval a

-- | Apply a 'StagedBuiltinName' to a list of 'Value's.
applyStagedBuiltinName :: PLC.StagedBuiltinName -> [Plain Value] -> CekM ConstAppResultDef
applyStagedBuiltinName (PLC.DynamicStagedBuiltinName name) args = do
    DynamicBuiltinNameMeaning sch x <- lookupDynamicBuiltinName name
    evaluateInCekM $ applyTypeSchemed sch x args
applyStagedBuiltinName (PLC.StaticStagedBuiltinName  name) args =
    evaluateInCekM $ applyBuiltinName name args

-- | Evaluate a term in an environment using the CEK machine.
evaluateCekIn
    :: CekEnv -> Plain Term -> Either CekMachineException EvaluationResultDef
evaluateCekIn cekEnv = runCekM cekEnv . computeCek []

-- | Evaluate a term using the CEK machine.
evaluateCek
    :: DynamicBuiltinNameMeanings -> Plain Term -> Either CekMachineException EvaluationResultDef
evaluateCek means = evaluateCekIn $ CekEnv means mempty

-- | Evaluate a term using the CEK machine. May throw a 'CekMachineException'.
unsafeEvaluateCek :: DynamicBuiltinNameMeanings -> Term Name () -> EvaluationResultDef
unsafeEvaluateCek = either throw id .* evaluateCek

-- The implementation is a bit of a hack.
readKnownCek
    :: KnownType a
    => DynamicBuiltinNameMeanings
    -> Term Name ()
    -> Either CekMachineException (EvaluationResult a)
readKnownCek means term = do
    res <- runReflectT $ readKnown (evaluateCek . mappend means) term
    case res of
        EvaluationFailure            -> Right EvaluationFailure
        EvaluationSuccess (Left err) -> Left $ MachineException appErr term where
            appErr = ConstAppMachineError $ UnreadableBuiltinConstAppError term err
        EvaluationSuccess (Right x)  -> Right $ EvaluationSuccess x

-- | Run a program using the CEK machine.
-- Calls 'evaluateCekCatch' under the hood.
runCek :: DynamicBuiltinNameMeanings -> Program Name () -> Either CekMachineException EvaluationResultDef
runCek means (Program _ _ term) = evaluateCek means term

-- | Run a program using the CEK machine. May throw a 'CekMachineException'.
-- Calls 'evaluateCek' under the hood.
unsafeRunCek :: DynamicBuiltinNameMeanings -> Program Name () -> EvaluationResultDef
unsafeRunCek means (Program _ _ term) = unsafeEvaluateCek means term
