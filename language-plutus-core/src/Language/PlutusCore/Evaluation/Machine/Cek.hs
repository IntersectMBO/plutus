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

{-# OPTIONS_GHC -Wno-unused-matches -Wno-unused-top-binds -Wno-unused-imports #-}  -- FIXME: remove

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

import           Debug.Trace

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
    | FrameApplyBuiltin                                                          -- ^ @(builtin bn A V* _ M*)
      BuiltinName
      [Type TyName uni ExMemory]
      [Closure uni]                     -- Computed arguments as closures
      [Term TyName Name uni ExMemory]   -- Remaining arguments
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
extendVarEnv :: Name -> WithMemory Value uni -> VarEnv uni -> VarEnv uni -> VarEnv uni
extendVarEnv argName arg argVarEnv =
    insertByName argName $ Closure argVarEnv arg

-- | Look up a variable name in the environment.
lookupVarName :: Name -> CekM uni (Closure uni)
lookupVarName varName = do
    varEnv <- getVarEnv
    case lookupName varName varEnv of
        Nothing   -> throwingWithCause _MachineError
            OpenTermEvaluatedMachineError
            (Just . Var () $ varName)
        Just clos -> pure clos

-- | Look up a 'DynamicBuiltinName' in the environment.
lookupDynamicBuiltinName :: DynamicBuiltinName -> CekM uni (DynamicBuiltinNameMeaning uni)
lookupDynamicBuiltinName dynName = do
    DynamicBuiltinNameMeanings means <- asks _cekEnvMeans
    case Map.lookup dynName means of
        Nothing   -> throwingWithCause _MachineError err $ Just term where
            err  = OtherMachineError $ UnknownDynamicBuiltinNameErrorE dynName
            term = ApplyBuiltin () (DynBuiltinName dynName) [] [] -- FIXME
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
computeCek ctx t@(TyInst _ body ty) = do
    spendBudget BTyInst t (ExBudget 1 1) -- TODO
    computeCek (FrameTyInstArg ty : ctx) body
computeCek ctx t@(Apply _ fun arg) = do
    spendBudget BApply t (ExBudget 1 1) -- TODO
    varEnv <- getVarEnv
    computeCek (FrameApplyArg varEnv arg : ctx) fun
computeCek ctx t@(IWrap ann pat arg term) = do
    spendBudget BIWrap t (ExBudget 1 1) -- TODO
    computeCek (FrameIWrap ann pat arg : ctx) term
computeCek ctx t@(Unwrap _ term) = do
    spendBudget BUnwrap t (ExBudget 1 1) -- TODO
    computeCek (FrameUnwrap : ctx) term
computeCek ctx tyAbs@TyAbs{}       = returnCek ctx tyAbs
computeCek ctx lamAbs@LamAbs{}     = returnCek ctx lamAbs
computeCek ctx constant@Constant{} = returnCek ctx constant
computeCek ctx t@(ApplyBuiltin ann bn tys []) = do
    spendBudget BIWrap t (ExBudget 1 1) -- FIXME:  BIWrap
    applyBuiltin ann ctx bn tys []
computeCek ctx t@(ApplyBuiltin _ bn tys (arg:args)) = do
  spendBudget BIWrap t (ExBudget 1 1) -- FIXME:  BIWrap
  computeCek (FrameApplyBuiltin bn tys [] args : ctx) arg


computeCek _   err@Error{} =
    throwingWithCause _EvaluationError (UserEvaluationError CekEvaluationFailure) $ Just (void err)
computeCek ctx t@(Var _ varName)   = do
    spendBudget BVar t (ExBudget 1 1) -- TODO
    Closure newVarEnv term <- lookupVarName varName
    withVarEnv newVarEnv $ returnCek ctx term

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
returnCek (FrameTyInstArg ty : ctx) fun = instantiateEvaluate ctx ty fun
returnCek (FrameApplyArg argVarEnv arg : ctx) fun = do
    funVarEnv <- getVarEnv
    withVarEnv argVarEnv $ computeCek (FrameApplyFun funVarEnv fun : ctx) arg
returnCek (FrameApplyFun funVarEnv fun : ctx) arg = do
    argVarEnv <- getVarEnv
    applyEvaluate funVarEnv argVarEnv ctx fun arg
returnCek (FrameIWrap ann pat arg : ctx) val =
    returnCek ctx $ IWrap ann pat arg val
returnCek (FrameUnwrap : ctx) dat = case dat of
    IWrap _ _ _ term -> returnCek ctx term
    term             ->
        throwingWithCause _MachineError NonWrapUnwrappedMachineError $ Just (void term)
returnCek (FrameApplyBuiltin bn tys closures terms : ctx) value = do
    varEnv <- getVarEnv  -- closure for just-computed argument
    let cl = Closure varEnv value  -- closure for just-computed argument
    case terms of
      []       -> applyBuiltin () ctx bn tys (cl:closures)
      arg:args -> computeCek (FrameApplyBuiltin bn tys (cl:closures) args : ctx) arg

applyBuiltin :: (GShow uni, GEq uni, DefaultUni <: uni, Closed uni, uni `Everywhere` ExMemoryUsage)
                 => ann
                 -> Context uni
                 -> BuiltinName
                 -> [Type TyName uni ExMemory]
                 -> [Closure uni]
                 -> CekM uni (Term TyName Name uni ())
applyBuiltin ann ctx bn tys args =
    let fixArgs = Prelude.map _closureValue . reverse
        fixedArgs = fixArgs args
    in  -- Debug.Trace.trace ("Calling " ++ show bn ++ " on " ++  show (length args) ++ " arguments") $
    do
      -- More careful for dynamic names?
      params <- builtinCostParams  -- FIXME: What are we doing with this?
      funEnv <- getVarEnv
      result <- applyStagedBuiltinName bn fixedArgs
      withVarEnv funEnv $
           case result of
             ConstAppSuccess res -> computeCek ctx res
             ConstAppStuck       -> error $ "returnCek ctx term: ConstAppStuck on " ++ show bn  ++ " (wrong number of arguments?)"
  -- check equality of number of params and args here and fail if
  -- different, otherwise zip together (costly?) and pass to foldArgs


-- Reverse the args?
-- foldArgs [] bn funEnv []                                      = applyBuiltinName undefined
-- foldArgs [] bn _ _                                            = error "Too many arguments to builtin"
-- foldArgs (param:params) bn funEnv (Closure varEnv arg : args) = withScopedArgIn funEnv varEnv
-- foldArgs _ _ _ []                                             = error "Too few arguments to builtin"

-- We have to fold withScopedArgIn over the values
-- Do we have a test case for the environment problem?

{- When we get to applyBuiltin, we have
      (a) A builtin name with arity (m,n) (number of type args, number of term args)
      (b) A chain of FrameApplyBuiltins of length n at the start of the context (we hope)
      (c) A list of values, also of length n
   We should ignore the type arguments (only required for typechecking) and
   wrap withScopedArgIn along the frames and the arguments, invoking the actual
   builtin when we get to the end.
-}
-- ######################################################################################################

-- | Instantiate a term with a type and proceed.
-- In case of 'TyAbs' just ignore the type. Otherwise check if the term is an
-- iterated application of a 'BuiltinName' to a list of 'Value's and, if succesful,
-- apply the term to the type via 'TyInst'.

-- ** FIXME: (a) How can we instantiate a polymorphic builtin?
-- (b)  If a builtin returns a polymorphic object, are we allowed to instantiate it?
--      What if we bind that object to a variable?  That should be OK if it's OK for abstractions.
instantiateEvaluate
    :: (GShow uni, GEq uni, DefaultUni <: uni, Closed uni, uni `Everywhere` ExMemoryUsage)
    => Context uni -> Type TyName uni ExMemory -> WithMemory Term uni -> CekM uni (Plain Term uni)
instantiateEvaluate ctx _ (TyAbs _ _ _ body) = computeCek ctx body
instantiateEvaluate ctx ty fun
    | isJust $ termAsPrimIterApp fun = returnCek ctx $ TyInst (memoryUsage () <> memoryUsage fun <> memoryUsage ty) fun ty
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
    argName <- freshName "arg"
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
applyEvaluate funVarEnv argVarEnv ctx (LamAbs _ name _ body) arg =
    withVarEnv (extendVarEnv name arg argVarEnv funVarEnv) $ computeCek ctx body
applyEvaluate funVarEnv argVarEnv ctx fun arg = error "applyEvaluate on non-lambda"
{-
     withScopedArgIn funVarEnv argVarEnv arg $ \arg' ->
        let term = Apply (memoryUsage () <> memoryUsage fun <> memoryUsage arg') fun arg'
        in case termAsPrimIterApp term of
            Nothing                       ->
                throwingWithCause _MachineError NonPrimitiveApplicationMachineError $ Just (void term)
            Just (IterApp headName spine) -> do
                constAppResult <- applyStagedBuiltinName headName spine
                case constAppResult of
                    ConstAppSuccess res -> computeCek ctx res
                    ConstAppStuck       -> returnCek ctx term
-}

-- | Apply a 'StagedBuiltinName' to a list of 'Value's.
applyStagedBuiltinName
    :: (GShow uni, GEq uni, DefaultUni <: uni, Closed uni, uni `Everywhere` ExMemoryUsage)
    => BuiltinName
    -> [WithMemory Value uni]
    -> CekM uni (ConstAppResult uni ExMemory)
applyStagedBuiltinName n@(DynBuiltinName name) args = do
    DynamicBuiltinNameMeaning sch x exX <- lookupDynamicBuiltinName name
    applyTypeSchemed n sch x exX args
applyStagedBuiltinName (StaticBuiltinName name) args = do
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
       , Typeable uni, uni `Everywhere` PrettyConst
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
