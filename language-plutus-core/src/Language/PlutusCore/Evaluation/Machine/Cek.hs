-- | The CEK machine.
-- Rules are the same as for the CK machine except we do not use substitution and use
-- environments instead.
-- The CEK machine relies on variables having non-equal 'Unique's whenever they have non-equal
-- string names. I.e. 'Unique's are used instead of string names. This is for efficiency reasons.
-- The type checker pass is a prerequisite.
-- Feeding ill-typed terms to the CEK machine will likely result in a 'MachineException'.
-- The CEK machine generates booleans along the way which might contain globally non-unique 'Unique's.
-- This is not a problem as the CEK machines handles name capture by design.
-- Dynamic extensions to the set of built-ins are allowed.
-- In case an unknown dynamic built-in is encountered, an 'UnknownDynamicBuiltinNameError' is returned
-- (wrapped in 'OtherMachineError').

{-# LANGUAGE ConstraintKinds       #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE UndecidableInstances  #-}

module Language.PlutusCore.Evaluation.Machine.Cek
    ( EvaluationResult(..)
    , EvaluationResultDef
    , ErrorWithCause(..)
    , MachineError(..)
    , CekMachineException
    , EvaluationError(..)
    , CekUserError(..)
    , CekEvaluationException
    , ExBudgetState(..)
    , ExTally(..)
    , ExBudget(..)
    , ExRestrictingBudget(..)
    , ExBudgetMode(..)
    , Plain
    , WithMemory
    , extractEvaluationResult
    , cekEnvMeans
    , cekEnvVarEnv
    , exBudgetStateTally
    , exBudgetStateBudget
    , exBudgetCPU
    , exBudgetMemory
    , runCek
    , runCekCounting
    , evaluateCek
    , unsafeEvaluateCek
    , readKnownCek
    )
where

import           PlutusPrelude

import           Data.Text.Prettyprint.Doc
import           Language.PlutusCore.Constant
import           Language.PlutusCore.Core
import           Language.PlutusCore.Error
import           Language.PlutusCore.Evaluation.Machine.ExBudgeting
import           Language.PlutusCore.Evaluation.Machine.Exception
import           Language.PlutusCore.Evaluation.Machine.ExMemory
import           Language.PlutusCore.Evaluation.Result
import           Language.PlutusCore.Name
import           Language.PlutusCore.Pretty
import           Language.PlutusCore.View

import           Control.Lens.Operators
import           Control.Lens.Setter
import           Control.Lens.TH                                    (makeLenses)
import           Control.Monad.Except
import           Control.Monad.Reader
import           Control.Monad.State.Strict
import           Data.HashMap.Monoidal
import qualified Data.Map                                           as Map

data CekUserError
    = CekOutOfExError ExRestrictingBudget ExBudget
    | CekEvaluationFailure -- ^ Error has been called.
    deriving (Show, Eq)

-- | The CEK machine-specific 'MachineException'.
type CekMachineException = MachineException UnknownDynamicBuiltinNameError

-- | The CEK machine-specific 'EvaluationException'.
type CekEvaluationException = EvaluationException UnknownDynamicBuiltinNameError CekUserError

instance Pretty CekUserError where
    pretty (CekOutOfExError (ExRestrictingBudget res) b) =
        group $ "The limit" <+> prettyClassicDef res <+> "was reached by the execution environment. Final state:" <+> prettyClassicDef b
    pretty CekEvaluationFailure = "The provided Plutus code called 'error'."

-- | A 'Value' packed together with the environment it's defined in.
data Closure = Closure
    { _closureVarEnv :: VarEnv
    , _closureValue  :: WithMemory Value
    }

-- | Variable environments used by the CEK machine.
-- Each row is a mapping from the 'Unique' representing a variable to a 'Closure'.
type VarEnv = UniqueMap TermUnique Closure

-- | The environment the CEK machine runs in.
data CekEnv = CekEnv
    { _cekEnvMeans      :: DynamicBuiltinNameMeanings
    , _cekEnvVarEnv     :: VarEnv
    , _cekEnvBudgetMode :: ExBudgetMode
    }

makeLenses ''CekEnv

-- | The monad the CEK machine runs in. State is inside the ExceptT, so we can
-- get it back in case of error.
type CekM = ReaderT CekEnv (ExceptT CekEvaluationException (State ExBudgetState))

instance SpendBudget CekM where
    spendBudget key term budget = do
        modifying exBudgetStateTally
                (<> (ExTally (singleton key budget)))
        newBudget <- exBudgetStateBudget <%= (<> budget)
        mode <- view cekEnvBudgetMode
        case mode of
            Counting -> pure ()
            Restricting resb ->
                when (exceedsBudget resb newBudget) $
                    throwingWithCause _EvaluationError (UserEvaluationError (CekOutOfExError resb newBudget)) (Just $ void term)

data Frame
    = FrameApplyFun VarEnv (WithMemory Value)                            -- ^ @[V _]@
    | FrameApplyArg VarEnv (WithMemory Term)                             -- ^ @[_ N]@
    | FrameTyInstArg (Type TyName ExMemory)                              -- ^ @{_ A}@
    | FrameUnwrap                                                        -- ^ @(unwrap _)@
    | FrameIWrap ExMemory (Type TyName ExMemory) (Type TyName ExMemory)  -- ^ @(iwrap A B _)@

type Context = [Frame]

runCekM
    :: forall a
     . CekEnv
    -> ExBudgetState
    -> CekM a
    -> (Either CekEvaluationException a, ExBudgetState)
runCekM env s a = runState (runExceptT $ runReaderT a env) s

-- | Get the current 'VarEnv'.
getVarEnv :: CekM VarEnv
getVarEnv = asks _cekEnvVarEnv

-- | Set a new 'VarEnv' and proceed.
withVarEnv :: VarEnv -> CekM a -> CekM a
withVarEnv venv = local (set cekEnvVarEnv venv)

-- | Extend an environment with a variable name, the value the variable stands for
-- and the environment the value is defined in.
extendVarEnv :: Name ExMemory -> WithMemory Value -> VarEnv -> VarEnv -> VarEnv
extendVarEnv argName arg argVarEnv =
    insertByName argName $ Closure argVarEnv arg

-- | Look up a variable name in the environment.
lookupVarName :: Name ExMemory -> CekM Closure
lookupVarName varName = do
    varEnv <- getVarEnv
    case lookupName varName varEnv of
        Nothing   -> throwingWithCause _MachineError
            OpenTermEvaluatedMachineError
            (Just . Var () $ void varName)
        Just clos -> pure clos

-- | Look up a 'DynamicBuiltinName' in the environment.
lookupDynamicBuiltinName :: DynamicBuiltinName -> CekM DynamicBuiltinNameMeaning
lookupDynamicBuiltinName dynName = do
    DynamicBuiltinNameMeanings means <- asks _cekEnvMeans
    case Map.lookup dynName means of
        Nothing   -> throwingWithCause _MachineError err $ Just term where
            err  = OtherMachineError $ UnknownDynamicBuiltinNameErrorE dynName
            term = Builtin () $ DynBuiltinName () dynName
        Just mean -> pure mean

-- | The computing part of the CEK machine.
-- Either
-- 1. adds a frame to the context and calls 'computeCek' ('TyInst', 'Apply', 'IWrap', 'Unwrap')
-- 2. calls 'returnCek' on values ('TyAbs', 'LamAbs', 'Constant')
-- 3. returns 'EvaluationFailure' ('Error')
-- 4. looks up a variable in the environment and calls 'returnCek' ('Var')
computeCek :: Context -> WithMemory Term -> CekM (Plain Term)
computeCek con t@(TyInst _ body ty) = do
    spendBudget BTyInst t (ExBudget 1 1) -- TODO
    computeCek (FrameTyInstArg ty : con) body
computeCek con t@(Apply _ fun arg) = do
    spendBudget BApply t (ExBudget 1 1) -- TODO
    varEnv <- getVarEnv
    computeCek (FrameApplyArg varEnv arg : con) fun
computeCek con t@(IWrap ann pat arg term) = do
    spendBudget BIWrap t (ExBudget 1 1) -- TODO
    computeCek (FrameIWrap ann pat arg : con) term
computeCek con t@(Unwrap _ term) = do
    spendBudget BUnwrap t (ExBudget 1 1) -- TODO
    computeCek (FrameUnwrap : con) term
computeCek con tyAbs@TyAbs{}       = returnCek con tyAbs
computeCek con lamAbs@LamAbs{}     = returnCek con lamAbs
computeCek con constant@Constant{} = returnCek con constant
computeCek con bi@Builtin{}        = returnCek con bi
computeCek _   err@Error{} =
    throwingWithCause _EvaluationError (UserEvaluationError CekEvaluationFailure) $ Just (void err)
computeCek con t@(Var _ varName)   = do
    spendBudget BVar t (ExBudget 1 1) -- TODO
    Closure newVarEnv term <- lookupVarName varName
    withVarEnv newVarEnv $ returnCek con term

-- | The returning part of the CEK machine.
-- Returns 'EvaluationSuccess' in case the context is empty, otherwise pops up one frame
-- from the context and either
-- 1. performs reduction and calls 'computeCek' ('FrameTyInstArg', 'FrameApplyFun', 'FrameUnwrap')
-- 2. performs a constant application and calls 'returnCek' ('FrameTyInstArg', 'FrameApplyFun')
-- 3. puts 'FrameApplyFun' on top of the context and proceeds with the argument from 'FrameApplyArg'
-- 4. grows the resulting term ('FrameWrap')
returnCek :: Context -> WithMemory Value -> CekM (Plain Term)
returnCek [] res = pure $ void res
returnCek (FrameTyInstArg ty : con) fun = instantiateEvaluate con ty fun
returnCek (FrameApplyArg argVarEnv arg : con) fun = do
    funVarEnv <- getVarEnv
    withVarEnv argVarEnv $ computeCek (FrameApplyFun funVarEnv fun : con) arg
returnCek (FrameApplyFun funVarEnv fun : con) arg = do
    argVarEnv <- getVarEnv
    applyEvaluate funVarEnv argVarEnv con fun arg
returnCek (FrameIWrap ann pat arg : con) val =
    returnCek con $ IWrap ann pat arg val
returnCek (FrameUnwrap : con) dat = case dat of
    IWrap _ _ _ term -> returnCek con term
    term             ->
        throwingWithCause _MachineError NonWrapUnwrappedMachineError $ Just (void term)

-- | Instantiate a term with a type and proceed.
-- In case of 'TyAbs' just ignore the type. Otherwise check if the term is an
-- iterated application of a 'BuiltinName' to a list of 'Value's and, if succesful,
-- apply the term to the type via 'TyInst'.
instantiateEvaluate
    :: Context -> Type TyName ExMemory -> WithMemory Term -> CekM (Plain Term)
instantiateEvaluate con _ (TyAbs _ _ _ body) = computeCek con body
instantiateEvaluate con ty fun
    | isJust $ termAsPrimIterApp fun = returnCek con $ TyInst (memoryUsage () <> memoryUsage fun <> memoryUsage ty) fun ty
    | otherwise                      =
        throwingWithCause _MachineError NonPrimitiveInstantiationMachineError $ Just (void fun)

-- | Apply a function to an argument and proceed.
-- If the function is a 'LamAbs', then extend the current environment with a new variable and proceed.
-- If the function is not a 'LamAbs', then 'Apply' it to the argument and view this
-- as an iterated application of a 'BuiltinName' to a list of 'Value's.
-- If succesful, proceed with either this same term or with the result of the computation
-- depending on whether 'BuiltinName' is saturated or not.
applyEvaluate
    :: VarEnv
    -> VarEnv
    -> Context
    -> WithMemory Value
    -> WithMemory Value
    -> CekM (Plain Term)
applyEvaluate funVarEnv argVarEnv con (LamAbs _ name _ body) arg =
    withVarEnv (extendVarEnv name arg argVarEnv funVarEnv) $ computeCek con body
applyEvaluate funVarEnv _ con fun arg =
    let term = Apply (memoryUsage () <> memoryUsage fun <> memoryUsage arg) fun arg in
        case termAsPrimIterApp term of
            Nothing                       ->
                throwingWithCause _MachineError NonPrimitiveApplicationMachineError $ Just (void term)
            Just (IterApp headName spine) -> do
                constAppResult <- applyStagedBuiltinName headName spine
                withVarEnv funVarEnv $ case constAppResult of
                    ConstAppSuccess res -> computeCek con res
                    ConstAppStuck       -> returnCek con term

-- | Reduce a saturated application of a builtin function in the empty context.
computeInCekM :: EvaluateConstApp CekM ann -> CekM (ConstAppResult ann)
computeInCekM = runEvaluateT eval where
    eval means' = local (over cekEnvMeans $ mappend means') . computeCek [] . withMemory

-- | Apply a 'StagedBuiltinName' to a list of 'Value's.
applyStagedBuiltinName
    :: StagedBuiltinName
    -> [WithMemory Value]
    -> CekM (ConstAppResult ExMemory)
applyStagedBuiltinName n@(DynamicStagedBuiltinName name) args = do
    DynamicBuiltinNameMeaning sch x exX <- lookupDynamicBuiltinName name
    computeInCekM $ applyTypeSchemed
        n
        sch
        x
        exX
        args
applyStagedBuiltinName (StaticStagedBuiltinName name) args =
    computeInCekM $ applyBuiltinName
        name
        args

-- | Evaluate a term using the CEK machine and keep track of costing.
runCek
    :: DynamicBuiltinNameMeanings
    -> ExBudgetMode
    -> Plain Term
    -> (Either CekEvaluationException (Plain Term), ExBudgetState)
runCek means mode term =
    runCekM (CekEnv means mempty mode)
            (ExBudgetState mempty mempty)
        $ do
            spendBudget BAST memTerm (ExBudget 0 (termAnn memTerm))
            computeCek [] memTerm
    where
        memTerm = withMemory term

-- | Evaluate a term using the CEK machine in the 'Counting' mode.
runCekCounting
    :: DynamicBuiltinNameMeanings
    -> Plain Term
    -> (Either CekEvaluationException (Plain Term), ExBudgetState)
runCekCounting means = runCek means Counting

-- | Evaluate a term using the CEK machine.
evaluateCek
    :: DynamicBuiltinNameMeanings
    -> Plain Term
    -> Either CekEvaluationException (Plain Term)
evaluateCek means = fst . runCekCounting means

-- | Evaluate a term using the CEK machine. May throw a 'CekMachineException'.
unsafeEvaluateCek :: DynamicBuiltinNameMeanings -> Plain Term -> EvaluationResultDef
unsafeEvaluateCek means = either throw id . extractEvaluationResult . evaluateCek means

-- | Unlift a value using the CEK machine.
readKnownCek
    :: KnownType a
    => DynamicBuiltinNameMeanings
    -> Plain Term
    -> Either CekEvaluationException a
readKnownCek = readKnownBy evaluateCek
