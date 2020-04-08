-- | The CEK machine.
-- Rules are the same as for the CK machine except we do not use substitution and use
-- environments instead.
-- The CEK machine relies on variables having non-equal 'Unique's whenever they have non-equal
-- string names. I.e. 'Unique's are used instead of string names. This is for efficiency reasons.
-- The CEK machines handles name capture by design.
-- The type checker pass is a prerequisite.
-- Feeding ill-typed terms to the CEK machine will likely result in a 'MachineException'.
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
{-# LANGUAGE TypeOperators         #-}
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

import           Language.PlutusCore.Constant
import           Language.PlutusCore.Core
import           Language.PlutusCore.Error
import           Language.PlutusCore.Evaluation.Machine.ExBudgeting
import           Language.PlutusCore.Evaluation.Machine.Exception
import           Language.PlutusCore.Evaluation.Machine.ExMemory
import           Language.PlutusCore.Evaluation.Result
import           Language.PlutusCore.Mark
import           Language.PlutusCore.Name
import           Language.PlutusCore.Pretty
import           Language.PlutusCore.Quote
import           Language.PlutusCore.Subst
import           Language.PlutusCore.Universe
import           Language.PlutusCore.View

import           Control.Lens.Operators
import           Control.Lens.Setter
import           Control.Lens.TH                                    (makeLenses)
import           Control.Monad.Except
import           Control.Monad.Reader
import           Control.Monad.State.Strict
import           Data.HashMap.Monoidal
import qualified Data.Map                                           as Map
import           Data.Text.Prettyprint.Doc

{- Note [Scoping]
The CEK machine does not rely on the global uniqueness condition, so the renamer pass is not a
prerequisite. The CEK machine correctly handles name shadowing.
-}

data CekUserError
    = CekOutOfExError ExRestrictingBudget ExBudget
    | CekEvaluationFailure -- ^ Error has been called.
    deriving (Show, Eq)

-- | The CEK machine-specific 'MachineException'.
type CekMachineException uni = MachineException uni UnknownDynamicBuiltinNameError

-- | The CEK machine-specific 'EvaluationException'.
type CekEvaluationException uni = EvaluationException uni UnknownDynamicBuiltinNameError CekUserError

instance Pretty CekUserError where
    pretty (CekOutOfExError (ExRestrictingBudget res) b) =
        group $ "The limit" <+> prettyClassicDef res <+> "was reached by the execution environment. Final state:" <+> prettyClassicDef b
    pretty CekEvaluationFailure = "The provided Plutus code called 'error'."

-- | A 'Value' packed together with the environment it's defined in.
data Closure uni = Closure
    { _closureVarEnv :: VarEnv uni
    , _closureValue  :: WithMemory Value uni
    } deriving (Show)

-- | Variable environments used by the CEK machine.
-- Each row is a mapping from the 'Unique' representing a variable to a 'Closure'.
type VarEnv uni = UniqueMap TermUnique (Closure uni)

-- | The environment the CEK machine runs in.
data CekEnv uni = CekEnv
    { _cekEnvMeans             :: DynamicBuiltinNameMeanings uni
    , _cekEnvVarEnv            :: VarEnv uni
    , _cekEnvBudgetMode        :: ExBudgetMode
    , _cekEnvBuiltinCostParams :: CostModel
    }

makeLenses ''CekEnv

-- | The monad the CEK machine runs in. State is inside the ExceptT, so we can
-- get it back in case of error.
type CekM uni = ReaderT (CekEnv uni) (ExceptT (CekEvaluationException uni) (QuoteT (State ExBudgetState)))

instance SpendBudget (CekM uni) uni where
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
    builtinCostParams = view cekEnvBuiltinCostParams

data Frame uni
    = FrameApplyFun (VarEnv uni) (WithMemory Value uni)                          -- ^ @[V _]@
    | FrameApplyArg (VarEnv uni) (WithMemory Term uni)                           -- ^ @[_ N]@
    | FrameTyInstArg (Type TyName uni ExMemory)                                  -- ^ @{_ A}@
    | FrameUnwrap                                                                -- ^ @(unwrap _)@
    | FrameIWrap ExMemory (Type TyName uni ExMemory) (Type TyName uni ExMemory)  -- ^ @(iwrap A B _)@
    deriving (Show)

type Context uni = [Frame uni]

runCekM
    :: forall a uni
     . CekEnv uni
    -> ExBudgetState
    -> CekM uni a
    -> (Either (CekEvaluationException uni) a, ExBudgetState)
runCekM env s a = runState (runQuoteT . runExceptT $ runReaderT a env) s

-- | Get the current 'VarEnv'.
getVarEnv :: CekM uni (VarEnv uni)
getVarEnv = asks _cekEnvVarEnv

-- | Set a new 'VarEnv' and proceed.
withVarEnv :: VarEnv uni -> CekM uni a -> CekM uni a
withVarEnv venv = local (set cekEnvVarEnv venv)

-- | Extend an environment with a variable name, the value the variable stands for
-- and the environment the value is defined in.
extendVarEnv :: Name ExMemory -> WithMemory Value uni -> VarEnv uni -> VarEnv uni -> VarEnv uni
extendVarEnv argName arg argVarEnv =
    insertByName argName $ Closure argVarEnv arg

-- | Look up a variable name in the environment.
lookupVarName :: Name ExMemory -> CekM uni (Closure uni)
lookupVarName varName = do
    varEnv <- getVarEnv
    case lookupName varName varEnv of
        Nothing   -> throwingWithCause _MachineError
            OpenTermEvaluatedMachineError
            (Just . Var () $ void varName)
        Just clos -> pure clos

-- | Look up a 'DynamicBuiltinName' in the environment.
lookupDynamicBuiltinName :: DynamicBuiltinName -> CekM uni (DynamicBuiltinNameMeaning uni)
lookupDynamicBuiltinName dynName = do
    DynamicBuiltinNameMeanings means <- asks _cekEnvMeans
    case Map.lookup dynName means of
        Nothing   -> throwingWithCause _MachineError err $ Just term where
            err  = OtherMachineError $ UnknownDynamicBuiltinNameErrorE dynName
            term = Builtin () $ DynBuiltinName () dynName
        Just mean -> pure mean

-- See Note [Scoping].
-- | Instantiate all the free variables of a term by looking them up in an environment.
dischargeVarEnv :: VarEnv uni -> WithMemory Term uni -> WithMemory Term uni
dischargeVarEnv varEnv =
    -- We recursively discharge the environments of closures, but we will gradually end up doing
    -- this to terms which have no free variables remaining, at which point we won't call this
    -- substitution function any more and so we will terminate.
    termSubstFreeNames $ \name -> do
        Closure varEnv' term' <- lookupName name varEnv
        Just $ dischargeVarEnv varEnv' term'

-- | The computing part of the CEK machine.
-- Either
-- 1. adds a frame to the context and calls 'computeCek' ('TyInst', 'Apply', 'IWrap', 'Unwrap')
-- 2. calls 'returnCek' on values ('TyAbs', 'LamAbs', 'Constant')
-- 3. returns 'EvaluationFailure' ('Error')
-- 4. looks up a variable in the environment and calls 'returnCek' ('Var')
computeCek
    :: (GShow uni, GEq uni, DefaultUni <: uni, Closed uni, uni `Everywhere` ExMemoryUsage)
    => Context uni -> WithMemory Term uni -> CekM uni (Plain Term uni)
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
returnCek
    :: (GShow uni, GEq uni, DefaultUni <: uni, Closed uni, uni `Everywhere` ExMemoryUsage)
    => Context uni -> WithMemory Value uni -> CekM uni (Plain Term uni)
-- Instantiate all the free variable of the resulting term in case there are any.
returnCek [] res = getVarEnv <&> \varEnv -> void $ dischargeVarEnv varEnv res
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
    :: (GShow uni, GEq uni, DefaultUni <: uni, Closed uni, uni `Everywhere` ExMemoryUsage)
    => Context uni -> Type TyName uni ExMemory -> WithMemory Term uni -> CekM uni (Plain Term uni)
instantiateEvaluate con _ (TyAbs _ _ _ body) = computeCek con body
instantiateEvaluate con ty fun
    | isJust $ termAsPrimIterApp fun = returnCek con $ TyInst (memoryUsage () <> memoryUsage fun <> memoryUsage ty) fun ty
    | otherwise                      =
        throwingWithCause _MachineError NonPrimitiveInstantiationMachineError $ Just (void fun)

{- Note [Saved mapping example]
Consider a polymorphic built-in function @id@, whose type signature on the Plutus side is

    id : all a. a -> a

Notation:

- the variable environment is denoted as @{ <var> :-> (<env>, <value>), ... }@
- the context is denoted as a Haskell list of 'Frame's
- 'computeCek' is denoted as @(|>)@
- 'returnCek' is denoted as @(<|)@

When evaluating

    id {integer -> integer} ((\(i : integer) (j : integer) -> i) 1) 0

We encounter the following state:

    { i :-> ({}, 1) }
    [ FrameApplyFun {} (id {integer -> integer})
    , FrameApplyArg {} 0
    ] |> \(j : integer) -> i

and transition it into

    { arg :-> ({ i :-> ({}, 1) }, \(j : integer) -> i) }
    [ FrameApplyArg {} 0
    ] <| id {integer -> integer} arg

i.e. if the argument is not a constant, then we create a new variable, save the old environment in
the closure of that variable and apply the function to the variable. This allows to restore the old
environment @{ i :-> ({}, 1) }@ latter when we start evaluating @arg 0@, which expands to

    (\(j : integer) -> i)) 0

which evaluates to @1@ in the old environment.
-}

-- See Note [Saved mapping example].
-- See https://github.com/input-output-hk/plutus/issues/1882 for discussion
-- | If an argument to a built-in function is a constant, then feed it directly to the continuation
-- that handles the argument and invoke the continuation in the caller's environment.
-- Otherwise create a fresh variable, save the environment of the argument in a closure, feed
-- the created variable to the continuation and invoke the continuation in the caller's environment
-- extended with a mapping from the created variable to the closure (i.e. original argument +
-- its environment). The "otherwise" is only supposed to happen when handling an argument to a
-- polymorphic built-in function.
withScopedArgIn
    :: VarEnv uni                            -- ^ The caller's envorinment.
    -> VarEnv uni                            -- ^ The argument's environment.
    -> WithMemory Value uni                  -- ^ The argument.
    -> (WithMemory Value uni -> CekM uni a)  -- ^ A continuation handling the argument.
    -> CekM uni a
withScopedArgIn funVarEnv _         arg@Constant{} k = withVarEnv funVarEnv $ k arg
withScopedArgIn funVarEnv argVarEnv arg            k = do
    let cost = memoryUsage ()
    argName <- freshName cost "arg"
    withVarEnv (extendVarEnv argName arg argVarEnv funVarEnv) $ k (Var cost argName)

-- | Apply a function to an argument and proceed.
-- If the function is a 'LamAbs', then extend the current environment with a new variable and proceed.
-- If the function is not a 'LamAbs', then 'Apply' it to the argument and view this
-- as an iterated application of a 'BuiltinName' to a list of 'Value's.
-- If succesful, proceed with either this same term or with the result of the computation
-- depending on whether 'BuiltinName' is saturated or not.
applyEvaluate
    :: (GShow uni, GEq uni, DefaultUni <: uni, Closed uni, uni `Everywhere` ExMemoryUsage)
    => VarEnv uni
    -> VarEnv uni
    -> Context uni
    -> WithMemory Value uni
    -> WithMemory Value uni
    -> CekM uni (Plain Term uni)
applyEvaluate funVarEnv argVarEnv con (LamAbs _ name _ body) arg =
    withVarEnv (extendVarEnv name arg argVarEnv funVarEnv) $ computeCek con body
applyEvaluate funVarEnv argVarEnv con fun arg = do
    withScopedArgIn funVarEnv argVarEnv arg $ \arg' ->
        let term = Apply (memoryUsage () <> memoryUsage fun <> memoryUsage arg') fun arg'
        in case termAsPrimIterApp term of
            Nothing                       ->
                throwingWithCause _MachineError NonPrimitiveApplicationMachineError $ Just (void term)
            Just (IterApp headName spine) -> do
                constAppResult <- applyStagedBuiltinName headName spine
                case constAppResult of
                    ConstAppSuccess res -> computeCek con res
                    ConstAppStuck       -> returnCek con term

-- | Apply a 'StagedBuiltinName' to a list of 'Value's.
applyStagedBuiltinName
    :: (GShow uni, GEq uni, DefaultUni <: uni, Closed uni, uni `Everywhere` ExMemoryUsage)
    => StagedBuiltinName
    -> [WithMemory Value uni]
    -> CekM uni (ConstAppResult uni ExMemory)
applyStagedBuiltinName n@(DynamicStagedBuiltinName name) args = do
    DynamicBuiltinNameMeaning sch x exX <- lookupDynamicBuiltinName name
    applyTypeSchemed n sch x exX args
applyStagedBuiltinName (StaticStagedBuiltinName name) args = do
    params <- builtinCostParams
    applyBuiltinName params name args

-- | Evaluate a term using the CEK machine and keep track of costing.
runCek
    :: (GShow uni, GEq uni, DefaultUni <: uni, Closed uni, uni `Everywhere` ExMemoryUsage)
    => DynamicBuiltinNameMeanings uni
    -> ExBudgetMode
    -> CostModel
    -> Plain Term uni
    -> (Either (CekEvaluationException uni) (Plain Term uni), ExBudgetState)
runCek means mode params term =
    runCekM (CekEnv means mempty mode params)
            (ExBudgetState mempty mempty)
        $ do
            -- We generate fresh variables during evaluation, see Note [Saved mapping example],
            -- hence making sure here that no accidental variable capture can occur.
            markNonFreshTerm term
            spendBudget BAST memTerm (ExBudget 0 (termAnn memTerm))
            computeCek [] memTerm
    where
        memTerm = withMemory term

-- | Evaluate a term using the CEK machine in the 'Counting' mode.
runCekCounting
    :: (GShow uni, GEq uni, DefaultUni <: uni, Closed uni, uni `Everywhere` ExMemoryUsage)
    => DynamicBuiltinNameMeanings uni
    -> CostModel
    -> Plain Term uni
    -> (Either (CekEvaluationException uni) (Plain Term uni), ExBudgetState)
runCekCounting means = runCek means Counting

-- | Evaluate a term using the CEK machine.
evaluateCek
    :: (GShow uni, GEq uni, DefaultUni <: uni, Closed uni, uni `Everywhere` ExMemoryUsage)
    => DynamicBuiltinNameMeanings uni
    -> CostModel
    -> Plain Term uni
    -> Either (CekEvaluationException uni) (Plain Term uni)
evaluateCek means params = fst . runCekCounting means params

-- | Evaluate a term using the CEK machine. May throw a 'CekMachineException'.
unsafeEvaluateCek
    :: ( GShow uni, GEq uni, DefaultUni <: uni, Closed uni, uni `Everywhere` ExMemoryUsage
       , Typeable uni, uni `Everywhere` Pretty
       )
    => DynamicBuiltinNameMeanings uni -> CostModel -> Plain Term uni -> EvaluationResultDef uni
unsafeEvaluateCek means params = either throw id . extractEvaluationResult . evaluateCek means params

-- | Unlift a value using the CEK machine.
readKnownCek
    :: ( GShow uni, GEq uni, DefaultUni <: uni, Closed uni, uni `Everywhere` ExMemoryUsage
       , KnownType uni a
       )
    => DynamicBuiltinNameMeanings uni
    -> CostModel
    -> Plain Term uni
    -> Either (CekEvaluationException uni) a
readKnownCek means params = evaluateCek means params >=> readKnown
