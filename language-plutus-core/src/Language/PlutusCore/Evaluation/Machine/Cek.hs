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
type CekMachineException uni = MachineException uni BuiltinError

-- | The CEK machine-specific 'EvaluationException'.
type CekEvaluationException uni = EvaluationException uni BuiltinError CekUserError

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
      (VarEnv uni)  -- Initial environment, used for evaluating every argument
      (VarEnv uni)  -- Environment extended with bindings for non-ground arguments: see Note [Saved mapping example]
      BuiltinName
      [Type  TyName uni ExMemory]      -- The types the builtin is to be instantiated at.  We don't really need these.
      [Value TyName Name uni ExMemory] -- Arguments we've computed so far.
      [Term  TyName Name uni ExMemory] -- Remaining arguments.
      -- See Note [Built-in application] below for an explanation of FrameAppplyBuiltin.
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
extendVarEnv argName arg argVarEnv env =
    insertByName argName (Closure argVarEnv arg) env

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
-- The 'term' argument is just there for the error message if the name's not found.
lookupDynamicBuiltinName :: Term TyName Name uni () -> DynamicBuiltinName -> CekM uni (DynamicBuiltinNameMeaning uni)
lookupDynamicBuiltinName term dynName = do
    DynamicBuiltinNameMeanings means <- asks _cekEnvMeans
    case Map.lookup dynName means of
        Nothing   -> throwingWithCause _MachineError err $ Just term where
                          err = OtherMachineError $ UnknownDynamicBuiltinName dynName
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

{- Note [Dropping environments of arguments]
The CEK machine sometimes keeps in the environment those variables that are no longer required.
This is a fundamental limitation of the CEK machine as it lacks garbage collection.
There are alternative machines that implement some form of environment cleaning (CESK, for example).
But if we're going to expore this space, it's better to jump straight to something close to actual
hardware than to deal with inherently inefficient abstract machines.

But if we could optimize the current evaluator at small development/maintenance cost, that would be
useful. One such opportunity is to drop the environment of a constant as a constant can't reference
any variables. So we do that in this line:

    computeCek con constant@Constant{} = withVarEnv mempty $ returnCek con constant

We can't drop the environment of a built-in function, because it can be polymorphic and thus can
receive arbitrary terms as arguments.

A 'TyAbs'- or 'LamAbs'-headed term may also reference free variables.

In the 'Var' case we drop the current environment, look up the variable and use the environment
stored in the looked up closure as per the normal control flow of the CEK machine.

Note that if we had polymorphic built-in types, we couldn't drop the environment of a constant as,
say, a `list nat` can contain arbitrary terms of type `nat` and thus can reference variables from
the environment. Polymorphic built-in types complicate evaluation in general as unlifting, say,
a `list integer` constant may require evaluating terms *inside* the constant (particularly, if that
constant was constructed by a built-in function). Similar complications associated with looking into
constants of polymorphic built-in types arise for other procedures (pretty-printing, type checking,
substitution, anything).
-}

-- See Note [Dropping environments of arguments].
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
computeCek ctx t@(ApplyBuiltin _ bn tys args) =
    -- FIXME (FAO @reactormonk): I've just re-used BApply for costing
    -- the use of FrameApplyBuiltin.  Maybe we should add a new
    -- constructor to `ExBudgetCategory` for that.
    case args of
        [] -> throwingWithCause _ConstAppError NullaryConstAppError $ Just (void t)
        arg:args' -> do
            spendBudget BApply t (ExBudget 1 1)
            varEnv <- getVarEnv
            computeCek (FrameApplyBuiltin varEnv varEnv bn tys [] args' : ctx) arg
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
-- Instantiate all the free variables of the resulting term in case there are any.
returnCek [] res = getVarEnv <&> \varEnv -> void $ dischargeVarEnv varEnv res
returnCek (FrameTyInstArg _ : ctx) fun =
    case fun of
      TyAbs _ _ _ body -> computeCek ctx body  -- NB: we're just ignoring the type here
      _                ->  throwingWithCause _MachineError NonTyAbsInstantiationMachineError $ Just (void fun)
returnCek (FrameApplyArg argVarEnv arg : ctx) fun = do
    funVarEnv <- getVarEnv
    withVarEnv argVarEnv $ computeCek (FrameApplyFun funVarEnv fun : ctx) arg
returnCek (FrameApplyFun funVarEnv fun : ctx) arg =
    case fun of
      LamAbs _ name _ body -> do
               argVarEnv <- getVarEnv
               withVarEnv (extendVarEnv name arg argVarEnv funVarEnv) $ computeCek ctx body
      _ ->  throwingWithCause _MachineError NonLambdaApplicationMachineError $ Just (Apply () (void fun) (void arg))
      -- FIXME: ^ error message looks like eg (1 2) instead of [(con 1) (con 2)]
returnCek (FrameIWrap ann pat arg : ctx) val =
    returnCek ctx $ IWrap ann pat arg val
returnCek (FrameUnwrap : ctx) dat = case dat of
    IWrap _ _ _ term -> returnCek ctx term
    term             ->
        throwingWithCause _MachineError NonWrapUnwrappedMachineError $ Just (void term)
returnCek (FrameApplyBuiltin initialEnv finalEnv bn tys values terms : ctx) value = do
    -- See Note [Built-in application] for an explanation of what's going on here.
    (values', finalEnv') <-
            case value of
              Constant{} -> pure (value:values, finalEnv)
              _ -> do
                argEnv  <- getVarEnv
                argName <- freshName "arg"
                let cost = memoryUsage ()
                pure (Var cost argName : values, extendVarEnv argName value argEnv finalEnv)
    case terms of
         []       -> applyBuiltin finalEnv' ctx bn tys (reverse values') -- We've accumulated the argument closures in reverse
         arg:args -> withVarEnv initialEnv $ computeCek (FrameApplyBuiltin initialEnv finalEnv' bn tys values' args : ctx) arg

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

    [[(builtin {id (fun (con integer) (con integer))} (lam i (con integer) (lam j (con integer) i))) 1] 0]
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
the closure of that variable and apply the function to the variable. This allows us to restore the old
environment @{ i :-> ({}, 1) }@ later when we start evaluating @arg 0@, which expands to

    (\(j : integer) -> i)) 0

which evaluates to @1@ in the old environment.
-}


{- Note [Built-in application]

-- See Note [Saved mapping example].
-- See https://github.com/input-output-hk/plutus/issues/1882 for discussion
-- See also https://github.com/input-output-hk/plutus/pull/1930

   Suppose we are evaluating an application of a built-in function B
   to a sequence of terms M_1, ..., M_n.  To a first approximation, we
   first evaluate each M_i to a value V_i and then call B on V_1, ...,
   V_n.  We do this using FrameApplyBuiltin frames.  These contain a
   list of the values V_1, ..., V_k which have alrady been evaluated
   and a list of yet-to-be-evaluated term arguments.  When we finally run
   out of term arguments, the function is called with the evaluated
   arguments.

   As pointed out in Note [Saved mapping example], we can't pass
   arbitrary values to built-ins.  To deal with this, the
   FrameApplyBuiltin frame also contains two environments: initialEnv,
   which is the environment in effect when evaluation of B M_1 ... M_n
   begin and finalEnv, which is to be used to carry on with the
   computation when the builtin has been evaluated.  As we process the
   arguments, we evaluate (in initialEnv) each one to a value V and
   check whether that is a constant or not.  If V is a constant, we
   save it directly in the list of arguments which will eventually be
   fed to the builtin.  If V isn't a constant, we generate a fresh
   variable v and extend finalEnv with a binding of v to a closure (V,
   env) (where env is the current environment) and save v in the list of
   arguments.

   Thus when we finally come to evaluate B, each argument will either be
   a constant or a variable, and finalEnv will be initialEnv extended
   with bindings for the variables.  We apply B to these arguments to
   obtain a result (possibly containing some of the input variables),
   and continue execution in finalEnv, which contains the values
   associated with all of the new variables.

   Currently each argument is evaluated in initialEnv.  However, we might
   be able to get away with using finalEnv instead, since every variable
   in finalEnv\initialEnv is fresh and thus should not appear in any of the
   input terms.

   Note also that because builtin applications have to be saturated
   with respect to both terms and types, a builtin cannot be
   instantiated (partially or fully) separately from application: all
   type parameters are supplied precisely at the point where the
   builtin is invoked.  Thus (in contrast to the situation with
   abstractions) instantiation of builtins cannot have any
   computational effect.  FrameApplyBuiltin frames contain the type
   parameters, but these are only used when generating a term for
   error messages.  We could possibly dispense with them altogether.

-}

applyBuiltin :: (GShow uni, GEq uni, DefaultUni <: uni, Closed uni, uni `Everywhere` ExMemoryUsage)
                 => VarEnv uni
                 -> Context uni
                 -> BuiltinName
                 -> [Type TyName uni ExMemory]
                 -> [Value TyName Name uni ExMemory]
                 -> CekM uni (Term TyName Name uni ())
applyBuiltin finalEnv ctx bn tys args =
    -- If there are too many/few types this will be caught by the
    -- builtin application machinery (and also the typechecker, if we
    -- run it).
    let term = ApplyBuiltin () bn (fmap void tys) (fmap void args) -- For error messages
    in do
      params <- builtinCostParams
      result <- case bn of
                  n@(DynBuiltinName name) -> do
                      DynamicBuiltinNameMeaning sch x exX <- lookupDynamicBuiltinName term name
                      applyTypeSchemed n sch x exX args
                  StaticBuiltinName name ->
                      applyBuiltinName params name args
      withVarEnv finalEnv $ computeCek ctx result

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
