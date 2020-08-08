{-# LANGUAGE TypeFamilies          #-}
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
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE UndecidableInstances  #-}

module Language.PlutusCore.Evaluation.Machine.Cek
    ( CekVal(..)
    , CekEvaluationException
    , EvaluationResult(..)
    , ErrorWithCause(..)
    , EvaluationError(..)
    , ExBudget(..)
    , ExBudgetMode(..)
    , ExRestrictingBudget(..)
    , ExTally(..)
    , exBudgetStateTally
    , extractEvaluationResult
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
import           Language.PlutusCore.MkPlc                          (mkIterApp, mkIterInst)
import           Language.PlutusCore.Name
import           Language.PlutusCore.Pretty
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

import           Data.Array

{- Note [Scoping]
   The CEK machine does not rely on the global uniqueness condition, so the renamer pass is not a
prerequisite. The CEK machine correctly handles name shadowing.
-}

type TermWithMem uni = WithMemory Term uni
type TypeWithMem uni = Type TyName uni ExMemory
type KindWithMem = Kind ExMemory

-- 'Values' for the modified CEK machine.
data CekVal uni =
    -- TODO: we probably want to store a @Some (ValueOf uni)@ here, but then we have trouble in
    -- 'readKnownCek'. I'll reconsider the way we deal with annotations once again.
    VCon (TermWithMem uni)
  | VTyAbs ExMemory TyName KindWithMem (TermWithMem uni) (CekValEnv uni)
  | VLamAbs ExMemory Name (TypeWithMem uni) (TermWithMem uni) (CekValEnv uni)
  | VIWrap ExMemory (TypeWithMem uni) (TypeWithMem uni) (CekVal uni)
  | VBuiltin
      ExMemory
      (CekValEnv uni)   -- Initial environment, used for evaluating every argument
      BuiltinName
      Int               -- Number of arguments to be provided (both types and terms)
      [TypeWithMem uni] -- The types the builtin is to be instantiated at.
                        -- We need these to construct a term if the machine is returning a stuck partial application.
      [CekVal uni]      -- Arguments we've computed so far.
    deriving (Show, Eq) -- Eq is just for tests.

instance (Closed uni, GShow uni, uni `Everywhere` PrettyConst) => PrettyBy PrettyConfigPlc (CekVal uni) where
    prettyBy cfg = prettyBy cfg . dischargeCekVal

type instance UniOf (CekVal uni) = uni

instance (Closed uni, uni `Everywhere` ExMemoryUsage) => FromConstant (CekVal uni) where
    fromConstant = VCon . fromConstant

instance AsConstant (CekVal uni) where
    asConstant (VCon term) = asConstant term
    asConstant _           = Nothing

instance ToExMemory (CekVal uni) where
    toExMemory = \case
        VCon t -> termAnn t
        VTyAbs ex _ _ _ _ -> ex
        VLamAbs ex _ _ _ _ -> ex
        VIWrap ex _ _ _ -> ex
        VBuiltin ex _ _ _ _ _ -> ex

type CekValEnv uni = UniqueMap TermUnique (CekVal uni)

-- Instantiate a builtin and then apply it to some arguments.  This assumes that
-- all type arguments come before term arguments, with no interleaving (and that
-- same assumption applies elsehwere, in VBuiltin, for example).  This is OK at the
-- moment, nut may change if we eventually support higher-rank builtins.
mkBuiltinApp :: ExMemory -> BuiltinName -> [TypeWithMem uni] -> [TermWithMem uni] -> TermWithMem uni
mkBuiltinApp ex bn tys args = mkIterApp ex (mkIterInst ex (Builtin ex bn) tys) args

-- See Note [Scoping].
-- | Instantiate all the free variables of a term by looking them up in an environment.
-- Mutually recursive with dischargeCekVal.
dischargeCekValEnv :: CekValEnv uni -> TermWithMem uni -> TermWithMem uni
dischargeCekValEnv valEnv =
    -- We recursively discharge the environments of Cek values, but we will gradually end up doing
    -- this to terms which have no free variables remaining, at which point we won't call this
    -- substitution function any more and so we will terminate.
    termSubstFreeNames $ \name -> do
        val <- lookupName name valEnv
        Just $ dischargeCekVal val

-- Convert a CekVal into a term by replacing all bound variables with the terms
-- they're bound to (which themselves have to be obtain by recursively discharging values).
dischargeCekVal :: CekVal uni -> TermWithMem uni
dischargeCekVal = \case
    VCon t                        -> t
    VTyAbs   ex tn k body env     -> TyAbs ex tn k (dischargeCekValEnv env body)
    VLamAbs  ex name ty body env  -> LamAbs ex name ty (dischargeCekValEnv env body)
    VIWrap   ex ty1 ty2 val       -> IWrap ex ty1 ty2 $ dischargeCekVal val
    VBuiltin ex _ bn _ types args -> mkBuiltinApp ex bn (reverse types) (fmap dischargeCekVal $ reverse args)
    {- We only discharge a value when (a) it's being returned by the machine, or
       (b) it's needed for an error message.  VBuiltin should only be discharged
       when the builtin is partially applied, and in that case we need to get
       the type and term arguments into the right order (they're accumulated in
       reverse).  In the fully-applied case, type arguments are ignored and term
       arguments are reversed in applyEvaluate. -}

data CekUserError
    = CekOutOfExError ExRestrictingBudget ExBudget
    | CekEvaluationFailure -- ^ Error has been called.
    deriving (Show, Eq)

-- | The CEK machine-specific 'EvaluationException'.
type CekEvaluationException uni =
    EvaluationException UnknownDynamicBuiltinNameError CekUserError (CekVal uni)

instance Pretty CekUserError where
    pretty (CekOutOfExError (ExRestrictingBudget res) b) =
        group $ "The limit" <+> prettyClassicDef res <+> "was reached by the execution environment. Final state:" <+> prettyClassicDef b
    pretty CekEvaluationFailure = "The provided Plutus code called 'error'."

-- | The environment the CEK machine runs in.
data CekEnv uni = CekEnv
    { cekEnvMeans              :: DynamicBuiltinNameMeanings (CekVal uni)
    , _cekEnvVarEnv            :: CekValEnv uni
    , _cekEnvBudgetMode        :: ExBudgetMode
    , _cekEnvBuiltinCostParams :: CostModel
    }

makeLenses ''CekEnv

-- | The monad the CEK machine runs in. State is inside the ExceptT, so we can
-- get it back in case of error.
type CekM uni = ReaderT (CekEnv uni) (ExceptT (CekEvaluationException uni) (State ExBudgetState))

instance SpendBudget (CekM uni) (CekVal uni) where
    builtinCostParams = view cekEnvBuiltinCostParams
    spendBudget key budget = do
        modifying exBudgetStateTally
                (<> (ExTally (singleton key budget)))
        newBudget <- exBudgetStateBudget <%= (<> budget)
        mode <- view cekEnvBudgetMode
        case mode of
            Counting -> pure ()
            Restricting resb ->
                when (exceedsBudget resb newBudget) $
                    throwingWithCause _EvaluationError
                        (UserEvaluationError $ CekOutOfExError resb newBudget)
                        Nothing  -- No value available for error

data Frame uni
    = FrameApplyFun (CekVal uni)                               -- ^ @[V _]@
    | FrameApplyArg (CekValEnv uni) (TermWithMem uni)          -- ^ @[_ N]@
    | FrameTyInstArg (TypeWithMem uni)                         -- ^ @{_ A}@
    | FrameUnwrap                                              -- ^ @(unwrap _)@
    | FrameIWrap ExMemory (TypeWithMem uni) (TypeWithMem uni)  -- ^ @(iwrap A B _)@
 deriving (Show)

type Context uni = [Frame uni]

runCekM
    :: forall a uni
     . CekEnv uni
    -> ExBudgetState
    -> CekM uni a
    -> (Either (CekEvaluationException uni) a, ExBudgetState)
runCekM env s a = runState (runExceptT $ runReaderT a env) s

-- | Get the current 'CekValEnv'.
getEnv :: CekM uni (CekValEnv uni)
getEnv = asks _cekEnvVarEnv

-- | Set a new 'VarEnv' and proceed.
withEnv :: CekValEnv uni -> CekM uni a -> CekM uni a
withEnv venv = local (set cekEnvVarEnv venv)

-- | Extend an environment with a variable name, the value the variable stands for
-- and the environment the value is defined in.
extendEnv :: Name -> CekVal uni -> CekValEnv uni -> CekValEnv uni
extendEnv argName arg  =
    insertByName argName arg

-- | Look up a variable name in the environment.
lookupVarName :: Name -> CekM uni (CekVal uni)
lookupVarName varName = do
    varEnv <- getEnv
    case lookupName varName varEnv of
        Nothing  -> throwingWithCause _MachineError OpenTermEvaluatedMachineError $ Nothing
                    -- No value available for error
        Just val -> pure val

-- | Look up a 'DynamicBuiltinName' in the environment.
lookupDynamicBuiltinName
    :: DynamicBuiltinName -> CekM uni (DynamicBuiltinNameMeaning (CekVal uni))
lookupDynamicBuiltinName dynName = do
    DynamicBuiltinNameMeanings means <- asks cekEnvMeans
    case Map.lookup dynName means of
        Nothing   -> throwingWithCause _MachineError err Nothing where
            err  = OtherMachineError $ UnknownDynamicBuiltinNameErrorE dynName
        Just mean -> pure mean

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

getArgsCount :: BuiltinName -> CekM uni Int
getArgsCount (StaticBuiltinName name) =
    pure $ builtinNameAritiesIncludingTypes ! name
getArgsCount (DynBuiltinName name) = do
    DynamicBuiltinNameMeaning sch _ _ <- lookupDynamicBuiltinName name
    pure $ countTypeAndTermArgs sch
-- TODO: have a table of dynamic arities so that we don't have to do this computation every time.

computeCek
    :: (GShow uni, GEq uni, DefaultUni <: uni, Closed uni, uni `Everywhere` ExMemoryUsage)
    => Context uni -> TermWithMem uni -> CekM uni (Plain Term uni)
-- s ; ρ ▻ {L A}  ↦ s , {_ A} ; ρ ▻ L
computeCek ctx (TyInst _ body ty) = do
    spendBudget BTyInst (ExBudget 1 1) -- TODO
    computeCek (FrameTyInstArg ty : ctx) body
-- s ; ρ ▻ [L M]  ↦  s , [_ (M,ρ)]  ; ρ ▻ L
computeCek ctx (Apply _ fun arg) = do
    spendBudget BApply (ExBudget 1 1) -- TODO
    env <- getEnv
    computeCek (FrameApplyArg env arg : ctx) fun
-- s ; ρ ▻ wrap A B L  ↦  s , wrap A B _ ; ρ ▻ L
computeCek ctx (IWrap ann pat arg term) = do
    spendBudget BIWrap (ExBudget 1 1) -- TODO
    computeCek (FrameIWrap ann pat arg : ctx) term
-- s ; ρ ▻ unwrap L  ↦  s , unwrap _ ; ρ ▻ L
computeCek ctx (Unwrap _ term) = do
    spendBudget BUnwrap (ExBudget 1 1) -- TODO
    computeCek (FrameUnwrap : ctx) term
-- s ; ρ ▻ abs α L  ↦  s ◅ abs α (L , ρ)
computeCek ctx (TyAbs ex tn k body)  = do
    env <- getEnv
    returnCek ctx (VTyAbs ex tn k body env)
-- s ; ρ ▻ lam x L  ↦  s ◅ lam x (L , ρ)
computeCek ctx (LamAbs ex name ty body)  = do
    env <- getEnv
    returnCek ctx (VLamAbs ex name ty body env)
-- s ; ρ ▻ con c  ↦  s ◅ con c
computeCek ctx c@Constant{} = returnCek ctx (VCon c)
computeCek ctx (Builtin ex bn)        = do
  env <- getEnv
  count <- getArgsCount bn
  returnCek ctx (VBuiltin ex env bn count [] [])
-- s ; ρ ▻ error A  ↦  <> A
computeCek _  Error{} =
    throwingWithCause _EvaluationError (UserEvaluationError CekEvaluationFailure) Nothing -- No value available for error
-- s ; ρ ▻ x  ↦  s ◅ ρ[ x ]
computeCek ctx (Var _ varName)   = do
    spendBudget BVar (ExBudget 1 1) -- TODO
    val <- lookupVarName varName
    returnCek ctx val

-- | The returning part of the CEK machine.
-- Returns 'EvaluationSuccess' in case the context is empty, otherwise pops up one frame
-- from the context and either
-- 1. performs reduction and calls 'computeCek' ('FrameTyInstArg', 'FrameApplyFun', 'FrameUnwrap')
-- 2. performs a constant application and calls 'returnCek' ('FrameTyInstArg', 'FrameApplyFun')
-- 3. puts 'FrameApplyFun' on top of the context and proceeds with the argument from 'FrameApplyArg'
-- 4. grows the resulting term ('FrameWrap')

returnCek
    :: (GShow uni, GEq uni, DefaultUni <: uni, Closed uni, uni `Everywhere` ExMemoryUsage)
    => Context uni -> CekVal uni -> CekM uni (Plain Term uni)
--- Instantiate all the free variable of the resulting term in case there are any.
-- . ◅ V           ↦  [] V
returnCek [] val = pure $ void $ dischargeCekVal val
-- s , {_ A} ◅ abs α M  ↦  s ; ρ ▻ M [ α / A ]*
returnCek (FrameTyInstArg ty : ctx) fun = instantiateEvaluate ctx ty fun
-- s , [_ (M,ρ)] ◅ V  ↦  s , [V _] ; ρ ▻ M
returnCek (FrameApplyArg argVarEnv arg : ctx) fun = do
    -- funVarEnv <- getEnv
    withEnv argVarEnv $ computeCek (FrameApplyFun fun : ctx) arg
-- s , [(lam x (M,ρ)) _] ◅ V  ↦  s ; ρ [ x  ↦  V ] ▻ M
returnCek (FrameApplyFun fun : ctx) arg = do
    applyEvaluate ctx fun arg
-- s , wrap A B _ ◅ V  ↦  s ◅ wrap A B V
returnCek (FrameIWrap ex pat arg : ctx) val =
    returnCek ctx $ VIWrap ex pat arg val
-- s , unwrap _ ◅ wrap A B V  ↦  s ◅ V
returnCek (FrameUnwrap : ctx) val =
    case val of
      VIWrap _ _ _ v -> returnCek ctx v
      _              ->
        throwingWithCause _MachineError NonWrapUnwrappedMachineError $ Just val

-- | Instantiate a term with a type and proceed.
-- In case of 'VTyAbs' just ignore the type; for 'VBuiltin', extend
-- the type arguments with the type, decrement the argument count,
-- and proceed; otherwise, it's an error.
instantiateEvaluate
    :: (GShow uni, GEq uni, DefaultUni <: uni, Closed uni, uni `Everywhere` ExMemoryUsage)
    => Context uni -> Type TyName uni ExMemory -> CekVal uni -> CekM uni (Plain Term uni)
instantiateEvaluate ctx _ (VTyAbs _ _ _ body env) = withEnv env $ computeCek ctx body -- FIXME: env?
instantiateEvaluate ctx ty (VBuiltin ex argEnv bn count tyargs args) =
    returnCek ctx $ VBuiltin ex argEnv bn (count-1) (ty:tyargs) args
    -- We should really check that the signature expects a type here, not a term.
    -- FIXME: what happens if count=0, ie if the final argument is a type?
    -- Also, what if count < 0?
instantiateEvaluate _ _ val =
        throwingWithCause _MachineError NonPolymorphicInstantiationMachineError $ Just val


-- | Apply a function to an argument and proceed.
-- If the function is a 'LamAbs', then extend the current environment with a new variable and proceed.
-- If the function is a 'Builtin', then check whether we've got the right number of arguments.
-- If we do, then ask the constant application machinery to apply it, and proceed with
-- the result (or throw an error if something goes wrong); if we don't, then add the new
-- argument to the VBuiltin and call returnCek to look for more arguments.
applyEvaluate
    :: (GShow uni, GEq uni, DefaultUni <: uni, Closed uni, uni `Everywhere` ExMemoryUsage)
    => Context uni
    -> CekVal uni   -- lsh of application
    -> CekVal uni   -- rhs of application
    -> CekM uni (Plain Term uni)
applyEvaluate ctx (VLamAbs _ name _ty body env) arg =
    withEnv (extendEnv name arg env) $ computeCek ctx body
applyEvaluate ctx val@(VBuiltin ex argEnv bn count tyargs args) arg = withEnv argEnv $ do
    let args' = arg:args
        count' = count - 1
        -- We're counting both type and term arguments here, so stricly
        -- we should check that we're expecting a term, not a type.
    if count' /= 0
        then returnCek ctx $ VBuiltin ex argEnv bn count' tyargs args'
        else do
            res <- applyBuiltinName bn (reverse args')
            case res of
                EvaluationSuccess t -> returnCek ctx t
                EvaluationFailure ->
                    throwingWithCause _EvaluationError (UserEvaluationError CekEvaluationFailure) $ Just val
applyEvaluate _ val _ = throwingWithCause _MachineError NonFunctionalApplicationMachineError $ Just val

-- | Apply a 'BuiltinName' to a list of 'Value's.
applyBuiltinName
    :: (GShow uni, GEq uni, DefaultUni <: uni, Closed uni, uni `Everywhere` ExMemoryUsage)
    => BuiltinName
    -> [CekVal uni]
    -> CekM uni (EvaluationResult (CekVal uni))
applyBuiltinName n@(DynBuiltinName name) args = do
    DynamicBuiltinNameMeaning sch x exX <- lookupDynamicBuiltinName name
    applyTypeSchemed n sch x exX args
applyBuiltinName (StaticBuiltinName name) args =
    applyStaticBuiltinName name args

-- | Evaluate a term using the CEK machine and keep track of costing.
runCek
    :: (GShow uni, GEq uni, DefaultUni <: uni, Closed uni, uni `Everywhere` ExMemoryUsage)
    => DynamicBuiltinNameMeanings (CekVal uni)
    -> ExBudgetMode
    -> CostModel
    -> Plain Term uni
    -> (Either (CekEvaluationException uni) (Plain Term uni), ExBudgetState)
runCek means mode params term =
    runCekM (CekEnv means mempty mode params)
            (ExBudgetState mempty mempty)
        $ do
            spendBudget BAST (ExBudget 0 (termAnn memTerm))
            computeCek [] memTerm
    where
        memTerm = withMemory term

-- | Evaluate a term using the CEK machine in the 'Counting' mode.
runCekCounting
    :: (GShow uni, GEq uni, DefaultUni <: uni, Closed uni, uni `Everywhere` ExMemoryUsage)
    => DynamicBuiltinNameMeanings (CekVal uni)
    -> CostModel
    -> Plain Term uni
    -> (Either (CekEvaluationException uni) (Plain Term uni), ExBudgetState)
runCekCounting means = runCek means Counting

-- | Evaluate a term using the CEK machine.
evaluateCek
    :: (GShow uni, GEq uni, DefaultUni <: uni, Closed uni, uni `Everywhere` ExMemoryUsage)
    => DynamicBuiltinNameMeanings (CekVal uni)
    -> CostModel
    -> Plain Term uni
    -> Either (CekEvaluationException uni) (Plain Term uni)
evaluateCek means params = fst . runCekCounting means params

-- | Evaluate a term using the CEK machine. May throw a 'CekMachineException'.
unsafeEvaluateCek
    :: ( GShow uni, GEq uni, DefaultUni <: uni
       , Closed uni
       , uni `Everywhere` ExMemoryUsage
       , uni `Everywhere` PrettyConst
       , Typeable uni
       )
    => DynamicBuiltinNameMeanings (CekVal uni)
    -> CostModel
    -> Plain Term uni
    -> EvaluationResult (Plain Term uni)
unsafeEvaluateCek means params = either throw id . extractEvaluationResult . evaluateCek means params

-- | Unlift a value using the CEK machine.
readKnownCek
    :: ( GShow uni, GEq uni, DefaultUni <: uni, Closed uni, uni `Everywhere` ExMemoryUsage
       , KnownType (Plain Term uni) a
       )
    => DynamicBuiltinNameMeanings (CekVal uni)
    -> CostModel
    -> Plain Term uni
    -> Either (CekEvaluationException uni) a
-- Calling 'withMemory' just to unify the monads that 'readKnown' and the CEK machine run in.
readKnownCek means params = evaluateCek means params >=> first (fmap $ VCon . withMemory) . readKnown
