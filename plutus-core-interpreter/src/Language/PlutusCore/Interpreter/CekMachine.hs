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

module Language.PlutusCore.Interpreter.CekMachine
    ( CekMachineException
    , EvaluationResultF (EvaluationSuccess, EvaluationFailure)
    , EvaluationResult
    , evaluateCekCatch
    , evaluateCek
    , readDynamicBuiltinCek
    , runCek
    ) where

import           Language.PlutusCore
import           Language.PlutusCore.Constant
import           Language.PlutusCore.Evaluation.MachineException
import           Language.PlutusCore.View
import           PlutusPrelude                                   hiding (hoist)

import           Control.Lens.TH                                 (makeLenses)
import           Control.Monad.Except
import           Control.Monad.Morph                             (hoist)
import           Control.Monad.Reader
import           Control.Monad.Trans                             (lift)
import           Data.IntMap                                     (IntMap)
import qualified Data.IntMap                                     as IntMap
import qualified Data.Map                                        as Map

type Plain f = f TyName Name ()

-- | The CEK machine-specific 'MachineException'.
type CekMachineException = MachineException UnknownDynamicBuiltinNameError

-- | A 'Value' packed together with the environment it's defined in.
data Closure = Closure
    { _closureVarEnv :: VarEnv
    , _closureValue  :: Plain Value
    }

-- | Variable environments used by the CEK machine.
-- Each row is a mapping from the 'Unique' representing a variable to a 'Closure'.
newtype VarEnv = VarEnv (IntMap Closure)

-- | The environment the CEK machine runs in.
data CekEnv = CekEnv
    { _cekEnvMeans  :: DynamicBuiltinNameMeanings
    , _cekEnvVarEnv :: VarEnv
    }

-- | The monad the CEK machine runs in.
type CekM = ReaderT CekEnv (Either CekMachineException)

data Frame
    = FrameApplyFun VarEnv (Plain Value)         -- ^ @[V _]@
    | FrameApplyArg VarEnv (Plain Term)          -- ^ @[_ N]@
    | FrameTyInstArg (Type TyName ())            -- ^ @{_ A}@
    | FrameUnwrap                                -- ^ @(unwrap _)@
    | FrameWrap () (TyName ()) (Type TyName ())  -- ^ @(wrap α A _)@

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
extendVarEnv argName arg argVarEnv (VarEnv oldVarEnv) =
    VarEnv $ IntMap.insert (unUnique $ nameUnique argName) (Closure argVarEnv arg) oldVarEnv

-- | Look up a variable name in the environment.
lookupVarName :: Name () -> CekM Closure
lookupVarName varName = do
    VarEnv varEnv <- getVarEnv
    case IntMap.lookup (unUnique $ nameUnique varName) varEnv of
        Nothing   -> throwError $ MachineException OpenTermEvaluatedMachineError (Var () varName)
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

-- | The computing part of the CEK machine.
-- Either
-- 1. adds a frame to the context and calls 'computeCek' ('TyInst', 'Apply', 'Wrap', 'Unwrap')
-- 2. calls 'returnCek' on values ('TyAbs', 'LamAbs', 'Constant')
-- 3. returns 'EvaluationFailure' ('Error')
-- 4. looks up a variable in the environment and calls 'returnCek' ('Var')
computeCek :: Context -> Plain Term -> CekM EvaluationResult
computeCek con (TyInst _ body ty)     = computeCek (FrameTyInstArg ty : con) body
computeCek con (Apply _ fun arg)      = do
    varEnv <- getVarEnv
    computeCek (FrameApplyArg varEnv arg : con) fun
computeCek con (Wrap ann tyn ty term) = computeCek (FrameWrap ann tyn ty : con) term
computeCek con (Unwrap _ term)        = computeCek (FrameUnwrap : con) term
computeCek con tyAbs@TyAbs{}          = returnCek con tyAbs
computeCek con lamAbs@LamAbs{}        = returnCek con lamAbs
computeCek con constant@Constant{}    = returnCek con constant
computeCek con bi@Builtin{}           = returnCek con bi
computeCek _   Error{}                = pure EvaluationFailure
computeCek con (Var _ varName)        = do
    Closure newVarEnv term <- lookupVarName varName
    withVarEnv newVarEnv $ returnCek con term

-- | The returning part of the CEK machine.
-- Returns 'EvaluationSuccess' in case the context is empty, otherwise pops up one frame
-- from the context and either
-- 1. performs reduction and calls 'computeCek' ('FrameTyInstArg', 'FrameApplyFun', 'FrameUnwrap')
-- 2. performs a constant application and calls 'returnCek' ('FrameTyInstArg', 'FrameApplyFun')
-- 3. puts 'FrameApplyFun' on top of the context and proceeds with the argument from 'FrameApplyArg'
-- 4. grows the resulting term ('FrameWrap')
returnCek :: Context -> Plain Value -> CekM EvaluationResult
returnCek []                                  res = pure $ EvaluationSuccess res
returnCek (FrameTyInstArg ty           : con) fun = instantiateEvaluate con ty fun
returnCek (FrameApplyArg argVarEnv arg : con) fun = do
    funVarEnv <- getVarEnv
    withVarEnv argVarEnv $ computeCek (FrameApplyFun funVarEnv fun : con) arg
returnCek (FrameApplyFun funVarEnv fun : con) arg = do
    argVarEnv <- getVarEnv
    applyEvaluate funVarEnv argVarEnv con fun arg
returnCek (FrameWrap ann tyn ty        : con) val = returnCek con $ Wrap ann tyn ty val
returnCek (FrameUnwrap                 : con) dat = case dat of
    Wrap _ _ _ term -> returnCek con term
    term            -> throwError $ MachineException NonWrapUnwrappedMachineError term

-- | Instantiate a term with a type and proceed.
-- In case of 'TyAbs' just ignore the type. Otherwise check if the term is an
-- iterated application of a 'BuiltinName' to a list of 'Value's and, if succesful,
-- apply the term to the type via 'TyInst'.
instantiateEvaluate :: Context -> Type TyName () -> Plain Term -> CekM EvaluationResult
instantiateEvaluate con _  (TyAbs _ _ _ body) = computeCek con body
instantiateEvaluate con ty fun
    | isJust $ termAsPrimIterApp fun = returnCek con $ TyInst () fun ty
    | otherwise                      =
        throwError $ MachineException NonPrimitiveInstantiationMachineError fun

-- | Apply a function to an argument and proceed.
-- If the function is a 'LamAbs', then extend the current environment with a new variable and proceed.
-- If the function is not a 'LamAbs', then 'Apply' it to the argument and view this
-- as an iterated application of a 'BuiltinName' to a list of 'Value's.
-- If succesful, proceed with either this same term or with the result of the computation
-- depending on whether 'BuiltinName' is saturated or not.
applyEvaluate
    :: VarEnv -> VarEnv -> Context -> Plain Value -> Plain Value -> CekM EvaluationResult
applyEvaluate funVarEnv argVarEnv con (LamAbs _ name _ body) arg =
    withVarEnv (extendVarEnv name arg argVarEnv funVarEnv) $ computeCek con body
applyEvaluate funVarEnv _         con fun                    arg =
    let term = Apply () fun arg in
        case termAsPrimIterApp term of
            Nothing                       ->
                throwError $ MachineException NonPrimitiveApplicationMachineError term
            Just (IterApp headName spine) -> do
                constAppResult <- runQuoteT $ applyStagedBuiltinName headName spine
                withVarEnv funVarEnv $ case constAppResult of
                    ConstAppSuccess res -> computeCek con res
                    ConstAppFailure     -> pure EvaluationFailure
                    ConstAppStuck       -> returnCek con term
                    ConstAppError   err ->
                        throwError $ MachineException (ConstAppMachineError err) term

evaluateInCekM :: Evaluate (Either CekMachineException) a -> CekM a
evaluateInCekM a =
    ReaderT $ \cekEnv ->
        let eval means' = evaluateCekCatchIn $
                cekEnv & cekEnvMeans %~ unionDynamicBuiltinNameMeanings means'
            in runEvaluate eval a

-- | Apply a 'StagedBuiltinName' to a list of 'Value's.
applyStagedBuiltinName :: StagedBuiltinName -> [Plain Value] -> QuoteT CekM ConstAppResult
applyStagedBuiltinName (DynamicStagedBuiltinName name) args = do
    DynamicBuiltinNameMeaning sch x <- lift $ lookupDynamicBuiltinName name
    hoist evaluateInCekM $ applyTypeSchemed sch x args
applyStagedBuiltinName (StaticStagedBuiltinName  name) args =
    hoist evaluateInCekM $ applyBuiltinName name args

-- | Evaluate a term in an environment using the CEK machine.
evaluateCekCatchIn
    :: CekEnv -> Plain Term -> Either CekMachineException EvaluationResult
evaluateCekCatchIn cekEnv = runCekM cekEnv . computeCek []

-- | Evaluate a term using the CEK machine.
evaluateCekCatch
    :: DynamicBuiltinNameMeanings -> Plain Term -> Either CekMachineException EvaluationResult
evaluateCekCatch means = evaluateCekCatchIn (CekEnv means $ VarEnv IntMap.empty)

-- | Evaluate a term using the CEK machine. May throw a 'CekMachineException'.
evaluateCek :: DynamicBuiltinNameMeanings -> Term TyName Name () -> EvaluationResult
evaluateCek = either throw id .* evaluateCekCatch

readDynamicBuiltinCek
    :: KnownDynamicBuiltinType dyn => Term TyName Name () -> Either CekMachineException (Maybe dyn)
readDynamicBuiltinCek = readDynamicBuiltin evaluateCekCatch

-- | Run a program using the CEK machine. May throw a 'CekMachineException'.
-- Calls 'evaluateCek' under the hood.
runCek :: DynamicBuiltinNameMeanings -> Program TyName Name () -> EvaluationResult
runCek means (Program _ _ term) = evaluateCek means term
