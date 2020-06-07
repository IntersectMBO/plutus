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
      (VarEnv uni)
      BuiltinName
      [Type TyName uni ExMemory]
      [Closure uni]                     -- Closures for the arguments we've computed so far.
      [Term TyName Name uni ExMemory]   -- Remaining arguments.
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
lookupDynamicBuiltinName :: Term TyName Name uni () -> DynamicBuiltinName -> CekM uni (DynamicBuiltinNameMeaning uni)
lookupDynamicBuiltinName term dynName = do
    DynamicBuiltinNameMeanings means <- asks _cekEnvMeans
    case Map.lookup dynName means of
        Nothing   -> throwingWithCause _MachineError err $ Just term where
                          err  = OtherMachineError $ UnknownDynamicBuiltinNameErrorE dynName
        -- 'term' is just here for the error message. Will including it have any effect on efficiency?
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
computeCek ctx t@(ApplyBuiltin ann bn tys args) =
    case args of
        [] -> do
            spendBudget (BBuiltin bn) t (ExBudget 1 1)
            -- FIXME: we're re-using BBuiltin for the argument-collecting process here and below.  Should we have a new constructor for this?
            varEnv <- getVarEnv
            applyBuiltin varEnv ann ctx bn tys []
        arg:args' -> do
            spendBudget (BBuiltin bn) t (ExBudget 1 1)
            varEnv <- getVarEnv
            withVarEnv varEnv $ computeCek (FrameApplyBuiltin varEnv bn tys [] args' : ctx) arg
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
returnCek (FrameTyInstArg ty : ctx) fun =
    case fun of
      TyAbs _ _ _ body -> computeCek ctx body  -- NB: we're just ignoring the type here
      _                ->  throwingWithCause _MachineError NonPrimitiveInstantiationMachineError $ Just (void fun)
returnCek (FrameApplyArg argVarEnv arg : ctx) fun = do
    funVarEnv <- getVarEnv
    withVarEnv argVarEnv $ computeCek (FrameApplyFun funVarEnv fun : ctx) arg
returnCek (FrameApplyFun funVarEnv fun : ctx) arg =
    case fun of
      LamAbs _ name _ body -> do
               argVarEnv <- getVarEnv
               withVarEnv (extendVarEnv name arg argVarEnv funVarEnv) $ computeCek ctx body
      _ ->  throwingWithCause _MachineError NonPrimitiveApplicationMachineError $ Just (Apply () (void fun) (void arg))
      -- FIXME: ^ error message looks like eg (1 2) instead of [(con 1) (con 2)]
returnCek (FrameIWrap ann pat arg : ctx) val =
    returnCek ctx $ IWrap ann pat arg val
returnCek (FrameUnwrap : ctx) dat = case dat of
    IWrap _ _ _ term -> returnCek ctx term
    term             ->
        throwingWithCause _MachineError NonWrapUnwrappedMachineError $ Just (void term)
returnCek (FrameApplyBuiltin env bn tys closures terms : ctx) value = do
    varEnv <- getVarEnv
    let closures' = Closure varEnv value : closures -- Save the closure for the argument we've just computed.
    case terms of
      []       -> applyBuiltin env () ctx bn tys (reverse closures') -- We've accumulated the argument closures in reverse
      arg:args -> withVarEnv env $ computeCek (FrameApplyBuiltin env bn tys closures' args : ctx) arg

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

-- UPDATE THE NOTE: see 1882 and 1930

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


-- If it's a standard builtin, all arguments should be (built-in)
-- values and this function will do nothing.  Can we use traverse or
-- something for this? We're simultaneously mapping across the args
-- and folding along the environment
getScopedArgs  -- We could perhaps fold this into `compute`: more efficient, but more complex?
               -- Let's leave it like this until we're sure it's correct.
    :: VarEnv uni              -- enviroment containing bindings for new variables
    -> [Closure uni]           -- original arguments
    -> CekM uni (VarEnv uni, [WithMemory Value uni])
getScopedArgs env0 args0 = getScopedArgs' args0 env0 [] where
    getScopedArgs' [] env newArgs = pure (env, reverse newArgs)
    getScopedArgs' (Closure argVarEnv arg : args) env newArgs =
        case arg of
          Constant{} -> getScopedArgs' args env (arg : newArgs)
          _ -> do
            argName <- freshName "arg"
            let cost = memoryUsage ()
                newArg = Var cost argName
                newEnv = extendVarEnv argName arg argVarEnv env
            getScopedArgs' args newEnv (newArg : newArgs)

applyBuiltin :: (GShow uni, GEq uni, DefaultUni <: uni, Closed uni, uni `Everywhere` ExMemoryUsage)
                 => VarEnv uni
                 -> ann
                 -> Context uni
                 -> BuiltinName
                 -> [Type TyName uni ExMemory]
                 -> [Closure uni]
                 -> CekM uni (Term TyName Name uni ())
applyBuiltin funEnv ann ctx bn tys args =
    -- If there are too many/few types this should be caught by the typechecker.
    let term = ApplyBuiltin () bn (fmap void tys) (fmap (void . _closureValue) args) -- For error messages
    in do
      -- Do we have to be more careful for dynamic names?
      (env', args') <- getScopedArgs funEnv args
      -- We could call getScopedArgs only in the case where tys is nonempty, relying on our assumption
      -- that non-polymorphic builtins only take builtin constants as arguments.
      params <- builtinCostParams
      result <- case bn of
                  n@(DynBuiltinName name) -> do
                      DynamicBuiltinNameMeaning sch x exX <- lookupDynamicBuiltinName term name
                      applyTypeSchemed n sch x exX args'
                  StaticBuiltinName name ->
                      applyBuiltinName params name args'
      case result of
             ConstAppSuccess res -> withVarEnv env' $ computeCek ctx res
             ConstAppStuck       -> throwingWithCause _ConstAppError TooFewArgumentsConstAppError $ Just term
                                 -- Overapplication is handled in applyTypeSchemed

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
