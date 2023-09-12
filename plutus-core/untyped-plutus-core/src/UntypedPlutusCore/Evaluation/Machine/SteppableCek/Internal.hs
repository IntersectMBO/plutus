-- editorconfig-checker-disable-file
-- | The CEK machine.
-- The CEK machine relies on variables having non-equal 'Unique's whenever they have non-equal
-- string names. I.e. 'Unique's are used instead of string names. This is for efficiency reasons.
-- The CEK machines handles name capture by design.
{-# LANGUAGE BangPatterns          #-}
{-# LANGUAGE ConstraintKinds       #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE ImplicitParams        #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NPlusKPatterns        #-}
{-# LANGUAGE NamedFieldPuns        #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE UndecidableInstances  #-}

module UntypedPlutusCore.Evaluation.Machine.SteppableCek.Internal
    ( CekState (..)
    , Context (..)
    , contextAnn
    , liftCek
    , PrimMonad (..)
    , lenContext
    , cekStateContext
    , cekStateAnn
    , runCekDeBruijn
    , computeCek
    , returnCek
    , tryError
    , mkCekTrans
    , CekTrans
    , nilSlippage
    , module UntypedPlutusCore.Evaluation.Machine.Cek.Internal
    )
where

import Control.Monad.Primitive
import PlutusCore.Builtin
import PlutusCore.DeBruijn
import PlutusCore.Evaluation.Machine.ExBudget
import PlutusCore.Evaluation.Machine.Exception
import PlutusCore.Evaluation.Machine.MachineParameters
import PlutusCore.Evaluation.Result
import PlutusPrelude
import Universe
import UntypedPlutusCore.Core
import UntypedPlutusCore.Evaluation.Machine.Cek.CekMachineCosts (CekMachineCosts,
                                                                 CekMachineCostsBase (..))
import UntypedPlutusCore.Evaluation.Machine.Cek.Internal hiding (Context (..), runCekDeBruijn,
                                                          transferArgStack)
import UntypedPlutusCore.Evaluation.Machine.Cek.StepCounter

import Control.Lens hiding (Context)
import Control.Monad
import Control.Monad.Except (MonadError, catchError)
import Data.List.Extras (wix)
import Data.Proxy
import Data.RandomAccessList.Class qualified as Env
import Data.Semigroup (stimes)
import Data.Text (Text)
import Data.Word (Word64)
import GHC.TypeNats

{- Note [Debuggable vs Original versions of CEK]

The debuggable version of CEK was created from copying over the original CEK/Internal.hs module
and modifying the `computeCek`, `returnCek` functions.
These functions were modified so as to execute a single step (Compute or Return resp.) and immediately
return with the CEK's machine new state (`CekState`), whereas previously these two functions would iteratively run to completion.

The interface otherwise remains the same. Moreover, the `Original.runCekDeBruijn` and `Debug.runCekDeBruijn` must behave equivalently.
-}

data CekState uni fun ann =
    -- loaded a term but not fired the cek yet
    Starting (NTerm uni fun ann)
    -- the next state is computing
    | Computing (Context uni fun ann) (CekValEnv uni fun ann) (NTerm uni fun ann)
    -- the next state is returning
    | Returning (Context uni fun ann) (CekValue uni fun ann)
    -- evaluation finished
    | Terminating (NTerm uni fun ())

instance Pretty (CekState uni fun ann) where
    pretty = \case
        Starting{}    -> "Starting"
        Computing{}   -> "Computing"
        Returning{}   -> "Returning"
        Terminating{} -> "Terminating"

-- | Similar to 'Cek.Internal.Context', but augmented with an 'ann'
data Context uni fun ann
    = FrameAwaitArg ann !(CekValue uni fun ann) !(Context uni fun ann)                         -- ^ @[V _]@
    | FrameAwaitFunTerm ann !(CekValEnv uni fun ann) !(NTerm uni fun ann) !(Context uni fun ann) -- ^ @[_ N]@
    | FrameAwaitFunValue ann !(CekValue uni fun ann) !(Context uni fun ann)
    | FrameForce ann !(Context uni fun ann)                                               -- ^ @(force _)@
    | FrameConstr ann !(CekValEnv uni fun ann) {-# UNPACK #-} !Word64 ![NTerm uni fun ann] !(ArgStack uni fun ann) !(Context uni fun ann)
    | FrameCases ann !(CekValEnv uni fun ann) ![NTerm uni fun ann] !(Context uni fun ann)
    | NoFrame

deriving stock instance (GShow uni, Everywhere uni Show, Show fun, Show ann, Closed uni)
    => Show (Context uni fun ann)

-- | Transfers an 'ArgStack' to a series of 'Context' frames.
transferArgStack :: ann -> ArgStack uni fun ann -> Context uni fun ann -> Context uni fun ann
transferArgStack ann = go
  where
    go EmptyStack c           = c
    go (ConsStack arg rest) c = go rest (FrameAwaitFunValue ann arg c)

computeCek
    :: forall uni fun ann s
    . (ThrowableBuiltins uni fun, GivenCekReqs uni fun ann s)
    => Context uni fun ann
    -> CekValEnv uni fun ann
    -> NTerm uni fun ann
    -> CekM uni fun s (CekState uni fun ann)
-- s ; ρ ▻ {L A}  ↦ s , {_ A} ; ρ ▻ L
computeCek !ctx !env (Var _ varName) = do
    stepAndMaybeSpend BVar
    val <- lookupVarName varName env
    pure $ Returning ctx val
computeCek !ctx !_ (Constant _ val) = do
    stepAndMaybeSpend BConst
    pure $ Returning ctx (VCon val)
computeCek !ctx !env (LamAbs _ name body) = do
    stepAndMaybeSpend BLamAbs
    pure $ Returning ctx (VLamAbs name body env)
computeCek !ctx !env (Delay _ body) = do
    stepAndMaybeSpend BDelay
    pure $ Returning ctx (VDelay body env)
-- s ; ρ ▻ lam x L  ↦  s ◅ lam x (L , ρ)
computeCek !ctx !env (Force _ body) = do
    stepAndMaybeSpend BForce
    pure $ Computing (FrameForce (termAnn body) ctx) env body
-- s ; ρ ▻ [L M]  ↦  s , [_ (M,ρ)]  ; ρ ▻ L
computeCek !ctx !env (Apply _ fun arg) = do
    stepAndMaybeSpend BApply
    pure $ Computing (FrameAwaitFunTerm (termAnn fun) env arg ctx) env fun
-- s ; ρ ▻ abs α L  ↦  s ◅ abs α (L , ρ)
-- s ; ρ ▻ con c  ↦  s ◅ con c
-- s ; ρ ▻ builtin bn  ↦  s ◅ builtin bn arity arity [] [] ρ
computeCek !ctx !_ (Builtin _ bn) = do
    stepAndMaybeSpend BBuiltin
    let meaning = lookupBuiltin bn ?cekRuntime
    -- 'Builtin' is fully discharged.
    pure $ Returning ctx (VBuiltin bn (Builtin () bn) meaning)
-- s ; ρ ▻ constr I T0 .. Tn  ↦  s , constr I _ (T1 ... Tn, ρ) ; ρ ▻ T0
computeCek !ctx !env (Constr ann i es) = do
    stepAndMaybeSpend BConstr
    case es of
        (t : rest) -> computeCek (FrameConstr ann env i rest EmptyStack ctx) env t
        _          -> returnCek ctx $ VConstr i EmptyStack
-- s ; ρ ▻ case S C0 ... Cn  ↦  s , case _ (C0 ... Cn, ρ) ; ρ ▻ S
computeCek !ctx !env (Case ann scrut cs) = do
    stepAndMaybeSpend BCase
    computeCek (FrameCases ann env cs ctx) env scrut
-- s ; ρ ▻ error A  ↦  <> A
computeCek !_ !_ (Error _) =
    throwing_ _EvaluationFailure

returnCek
    :: forall uni fun ann s
    . (ThrowableBuiltins uni fun, GivenCekReqs uni fun ann s)
    => Context uni fun ann
    -> CekValue uni fun ann
    -> CekM uni fun s (CekState uni fun ann)
--- Instantiate all the free variable of the resulting term in case there are any.
-- . ◅ V           ↦  [] V
returnCek NoFrame val = do
    spendAccumulatedBudget
    pure $ Terminating (dischargeCekValue val)
-- s , {_ A} ◅ abs α M  ↦  s ; ρ ▻ M [ α / A ]*
returnCek (FrameForce _ ctx) fun = forceEvaluate ctx fun
-- s , [_ (M,ρ)] ◅ V  ↦  s , [V _] ; ρ ▻ M
returnCek (FrameAwaitFunTerm _funAnn argVarEnv arg ctx) fun =
    -- MAYBE: perhaps it is worth here to merge the _funAnn with argAnn
    pure $ Computing (FrameAwaitArg (termAnn arg) fun ctx) argVarEnv arg
-- s , [(lam x (M,ρ)) _] ◅ V  ↦  s ; ρ [ x  ↦  V ] ▻ M
-- FIXME: add rule for VBuiltin once it's in the specification.
returnCek (FrameAwaitArg _ fun ctx) arg =
    applyEvaluate ctx fun arg
-- s , [_ V1 .. Vn] ◅ lam x (M,ρ)  ↦  s , [_ V2 .. Vn]; ρ [ x  ↦  V1 ] ▻ M
returnCek (FrameAwaitFunValue _ arg ctx) fun =
    applyEvaluate ctx fun arg
-- s , constr I V0 ... Vj-1 _ (Tj+1 ... Tn, ρ) ◅ Vj  ↦  s , constr i V0 ... Vj _ (Tj+2... Tn, ρ)  ; ρ ▻ Tj+1
returnCek (FrameConstr ann env i todo done ctx) e = do
    let done' = ConsStack e done
    case todo of
        (next : todo') -> computeCek (FrameConstr ann env i todo' done' ctx) env next
        _              -> returnCek ctx $ VConstr i done'
-- s , case _ (C0 ... CN, ρ) ◅ constr i V1 .. Vm  ↦  s , [_ V1 ... Vm] ; ρ ▻ Ci
returnCek (FrameCases ann env cs ctx) e = case e of
    (VConstr i args) -> case cs ^? wix i of
        Just t  ->
              let ctx' = transferArgStack ann args ctx
              in computeCek ctx' env t
        Nothing -> throwingDischarged _MachineError (MissingCaseBranch i) e
    _ -> throwingDischarged _MachineError NonConstrScrutinized e

-- | @force@ a term and proceed.
-- If v is a delay then compute the body of v;
-- if v is a builtin application then check that it's expecting a type argument,
-- and either calculate the builtin application or stick a 'Force' on top of its 'Term'
-- representation depending on whether the application is saturated or not,
-- if v is anything else, fail.
forceEvaluate
    :: forall uni fun ann s
    . (ThrowableBuiltins uni fun, GivenCekReqs uni fun ann s)
    => Context uni fun ann
    -> CekValue uni fun ann
    -> CekM uni fun s (CekState uni fun ann)
forceEvaluate !ctx (VDelay body env) =
    pure $ Computing ctx env body
forceEvaluate !ctx (VBuiltin fun term runtime) = do
    -- @term@ is fully discharged, and so @term'@ is, hence we can put it in a 'VBuiltin'.
    let term' = Force (termAnn term) term
    case runtime of
        -- It's only possible to force a builtin application if the builtin expects a type
        -- argument next.
        BuiltinExpectForce runtime' -> do
            -- We allow a type argument to appear last in the type of a built-in function,
            -- otherwise we could just assemble a 'VBuiltin' without trying to evaluate the
            -- application.
            res <- evalBuiltinApp fun term' runtime'
            pure $ Returning ctx res
        _ ->
            throwingWithCause _MachineError BuiltinTermArgumentExpectedMachineError (Just term')
forceEvaluate !_ val =
    throwingDischarged _MachineError NonPolymorphicInstantiationMachineError val

-- | Apply a function to an argument and proceed.
-- If the function is a lambda 'lam x ty body' then extend the environment with a binding of @v@
-- to x@ and call 'computeCek' on the body.
-- If the function is a builtin application then check that it's expecting a term argument,
-- and either calculate the builtin application or stick a 'Apply' on top of its 'Term'
-- representation depending on whether the application is saturated or not.
-- If v is anything else, fail.
applyEvaluate
    :: forall uni fun ann s
    . (ThrowableBuiltins uni fun, GivenCekReqs uni fun ann s)
    => Context uni fun ann
    -> CekValue uni fun ann   -- lhs of application
    -> CekValue uni fun ann   -- rhs of application
    -> CekM uni fun s (CekState uni fun ann)
applyEvaluate !ctx (VLamAbs _ body env) arg =
    pure $ Computing ctx (Env.cons arg env) body
-- Annotating @f@ and @exF@ with bangs gave us some speed-up, but only until we added a bang to
-- 'VCon'. After that the bangs here were making things a tiny bit slower and so we removed them.
applyEvaluate !ctx (VBuiltin fun term runtime) arg = do
    let argTerm = dischargeCekValue arg
        -- @term@ and @argTerm@ are fully discharged, and so @term'@ is, hence we can put it
        -- in a 'VBuiltin'.
        term' = Apply (termAnn term) term argTerm
    case runtime of
        -- It's only possible to apply a builtin application if the builtin expects a term
        -- argument next.
        BuiltinExpectArgument f -> do
            res <- evalBuiltinApp fun term' $ f arg
            pure $ Returning ctx res
        _ ->
            throwingWithCause _MachineError UnexpectedBuiltinTermArgumentMachineError (Just term')
applyEvaluate !_ val _ =
    throwingDischarged _MachineError NonFunctionalApplicationMachineError val

-- MAYBE: runCekDeBruijn can be shared between original&debug ceks by passing a `enterComputeCek` func.
runCekDeBruijn
    :: ThrowableBuiltins uni fun
    => MachineParameters CekMachineCosts fun (CekValue uni fun ann)
    -> ExBudgetMode cost uni fun
    -> EmitterMode uni fun
    -> NTerm uni fun ann
    -> (Either (CekEvaluationException NamedDeBruijn uni fun) (NTerm uni fun ()), cost, [Text])
runCekDeBruijn params mode emitMode term =
    runCekM params mode emitMode $ do
        spendBudgetCek BStartup $ runIdentity $ cekStartupCost ?cekCosts
        enterComputeCek NoFrame Env.empty term

-- See Note [Compilation peculiarities].
-- | The entering point to the CEK machine's engine.
enterComputeCek
    :: forall uni fun ann s
    . (ThrowableBuiltins uni fun, GivenCekReqs uni fun ann s)
    => Context uni fun ann
    -> CekValEnv uni fun ann
    -> NTerm uni fun ann
    -> CekM uni fun s (NTerm uni fun ())
enterComputeCek ctx env term = iterToFinalState $ Computing ctx env term
 where
   iterToFinalState :: CekState uni fun ann -> CekM uni fun s (NTerm uni fun ())
   iterToFinalState = cekTrans
                      >=>
                      \case
                          Terminating t -> pure t
                          x             -> iterToFinalState x

-- | A CEK parameter that turns the slippage optimization *off*.
--
-- This is needed in the case of the debugger, where the accounting/budgeting costs
-- must be *live* updated.
nilSlippage :: Slippage
-- Setting the slippage to 1 would also work and turn off slippage optimization.
nilSlippage = 0

-- the type of our state transition function, `s -> m s` , aka `Kleisli m a a`
type Trans m state = state -> m state
type CekTrans uni fun ann s = Trans (CekM uni fun s) (CekState uni fun ann)

-- | The state transition function of the machine.
cekTrans :: forall uni fun ann s
           . (ThrowableBuiltins uni fun, GivenCekReqs uni fun ann s)
           => CekTrans uni fun ann s
cekTrans = \case
    Starting term          -> pure $ Computing NoFrame Env.empty term
    Computing ctx env term -> computeCek ctx env term
    Returning ctx val      -> returnCek ctx val
    self@Terminating{}     -> pure self -- FINAL STATE, idempotent

-- | Based on the supplied arguments, initialize the CEK environment and
-- construct a state transition function.
-- Returns the constructed transition function paired with the methods to live access the running budget.
mkCekTrans
    :: forall cost uni fun ann m s
    . ( ThrowableBuiltins uni fun
      , PrimMonad m, s ~ PrimState m) -- the outer monad that initializes the transition function
    => MachineParameters CekMachineCosts fun (CekValue uni fun ann)
    -> ExBudgetMode cost uni fun
    -> EmitterMode uni fun
    -> Slippage
    -> m (CekTrans uni fun ann s, ExBudgetInfo cost uni fun s)
mkCekTrans (MachineParameters costs runtime) (ExBudgetMode getExBudgetInfo) (EmitterMode getEmitterMode) slippage = do
    exBudgetInfo@ExBudgetInfo{_exBudgetModeSpender, _exBudgetModeGetCumulative} <- liftPrim getExBudgetInfo
    CekEmitterInfo{_cekEmitterInfoEmit} <- liftPrim $ getEmitterMode _exBudgetModeGetCumulative
    ctr <- newCounter (Proxy @CounterSize)
    let ?cekRuntime = runtime
        ?cekEmitter = _cekEmitterInfoEmit
        ?cekBudgetSpender = _exBudgetModeSpender
        ?cekCosts = costs
        ?cekSlippage = slippage
        ?cekStepCounter = ctr
      in pure (cekTrans, exBudgetInfo)
         -- note that we do not call the final budget&emit getters like in `runCekM`,
         -- since we do not need it for our usecase.

-- * Helpers
------------

-- | Lift a CEK computation to a primitive.PrimMonad m
liftCek :: (PrimMonad m, PrimState m ~ s)  => CekM uni fun s a -> m a
liftCek= liftPrim . unCekM

cekStateContext :: Traversal' (CekState uni fun ann) (Context uni fun ann)
cekStateContext f = \case
    Computing k e t -> Computing <$> f k <*> pure e <*> pure t
    Returning k v   -> Returning <$> f k <*> pure v
    x               -> pure x

cekStateAnn :: CekState uni fun ann -> Maybe ann
cekStateAnn = \case
    Computing _ _ t -> pure $ termAnn t
    Returning ctx _ -> contextAnn ctx
    _               -> empty

contextAnn :: Context uni fun ann -> Maybe ann
contextAnn = \case
    FrameAwaitArg ann _ _       -> pure ann
    FrameAwaitFunTerm ann _ _ _ -> pure ann
    FrameAwaitFunValue ann _ _  -> pure ann
    FrameForce ann _            -> pure ann
    FrameConstr ann _ _ _ _ _   -> pure ann
    FrameCases ann _ _ _        -> pure ann
    NoFrame                     -> empty

lenContext :: Context uni fun ann -> Word
lenContext = go 0
    where
      go :: Word -> Context uni fun ann -> Word
      go !n = \case
              FrameAwaitArg _ _ k       -> go (n+1) k
              FrameAwaitFunTerm _ _ _ k -> go (n+1) k
              FrameAwaitFunValue _ _ k  -> go (n+1) k
              FrameForce _ k            -> go (n+1) k
              FrameConstr _ _ _ _ _ k   -> go (n+1) k
              FrameCases _ _ _ k        -> go (n+1) k
              NoFrame                   -> 0


-- * Duplicated functions from Cek.Internal module
-- FIXME: share these functions with Cek.Internal
-- preliminary testing shows that sharing slows down original cek

-- | A 'MonadError' version of 'try'.
--
-- TODO: remove when we switch to mtl>=2.3
tryError :: MonadError e m => m a -> m (Either e a)
tryError a = (Right <$> a) `catchError` (pure . Left)

cekStepCost :: CekMachineCosts -> StepKind -> ExBudget
cekStepCost costs = runIdentity . \case
    BConst   -> cekConstCost costs
    BVar     -> cekVarCost costs
    BLamAbs  -> cekLamCost costs
    BApply   -> cekApplyCost costs
    BDelay   -> cekDelayCost costs
    BForce   -> cekForceCost costs
    BBuiltin -> cekBuiltinCost costs
    BConstr  -> cekConstrCost costs
    BCase    -> cekCaseCost costs

-- | Call 'dischargeCekValue' over the received 'CekVal' and feed the resulting 'Term' to
-- 'throwingWithCause' as the cause of the failure.
throwingDischarged
    :: ThrowableBuiltins uni fun
    => AReview (EvaluationError CekUserError (MachineError fun)) t
    -> t
    -> CekValue uni fun ann
    -> CekM uni fun s x
throwingDischarged l t = throwingWithCause l t . Just . dischargeCekValue

-- | Look up a variable name in the environment.
lookupVarName
    :: forall uni fun ann s .
       ThrowableBuiltins uni fun
    => NamedDeBruijn -> CekValEnv uni fun ann -> CekM uni fun s (CekValue uni fun ann)
lookupVarName varName@(NamedDeBruijn _ varIx) varEnv =
    case varEnv `Env.indexOne` coerce varIx of
        Nothing  -> throwingWithCause _MachineError OpenTermEvaluatedMachineError $ Just var where
            var = Var () varName
        Just val -> pure val

-- | Take pieces of a possibly partial builtin application and either create a 'CekValue' using
-- 'makeKnown' or a partial builtin application depending on whether the built-in function is
-- fully saturated or not.
evalBuiltinApp
    :: (GivenCekReqs uni fun ann s, ThrowableBuiltins uni fun)
    => fun
    -> NTerm uni fun ()
    -> BuiltinRuntime (CekValue uni fun ann)
    -> CekM uni fun s (CekValue uni fun ann)
evalBuiltinApp fun term runtime = case runtime of
    BuiltinResult budgets getX -> do
        spendBudgetStreamCek (BBuiltinApp fun) budgets
        case getX of
            MakeKnownFailure logs err       -> do
                ?cekEmitter logs
                throwKnownTypeErrorWithCause term err
            MakeKnownSuccess x              -> pure x
            MakeKnownSuccessWithLogs logs x -> ?cekEmitter logs $> x
    _ -> pure $ VBuiltin fun term runtime
{-# INLINE evalBuiltinApp #-}

spendBudgetCek :: GivenCekSpender uni fun s => ExBudgetCategory fun -> ExBudget -> CekM uni fun s ()
spendBudgetCek = let (CekBudgetSpender spend) = ?cekBudgetSpender in spend

-- | Spend the budget that has been accumulated for a number of machine steps.
--
spendAccumulatedBudget :: (GivenCekReqs uni fun ann s) => CekM uni fun s ()
spendAccumulatedBudget = do
    let ctr = ?cekStepCounter
    iforCounter_ ctr spend
    resetCounter ctr
  where
    -- Making this a definition of its own causes it to inline better than actually writing it inline, for
    -- some reason.
    -- Skip index 7, that's the total counter!
    -- See Note [Structure of the step counter]
    {-# INLINE spend #-}
    spend !i !w = unless (i == (fromIntegral $ natVal $ Proxy @TotalCountIndex)) $
      let kind = toEnum i in spendBudgetCek (BStep kind) (stimes w (cekStepCost ?cekCosts kind))

-- | Accumulate a step, and maybe spend the budget that has accumulated for a number of machine steps, but only if we've exceeded our slippage.
stepAndMaybeSpend :: (GivenCekReqs uni fun ann s) => StepKind -> CekM uni fun s ()
stepAndMaybeSpend !kind = do
    -- See Note [Structure of the step counter]
    -- This generates let-expressions in GHC Core, however all of them bind unboxed things and
    -- so they don't survive further compilation, see https://stackoverflow.com/a/14090277
    let !counterIndex = fromEnum kind
        ctr = ?cekStepCounter
        !totalStepIndex = fromIntegral $ natVal (Proxy @TotalCountIndex)
    !unbudgetedStepsTotal <-  modifyCounter totalStepIndex (+1) ctr
    _ <- modifyCounter counterIndex (+1) ctr
    -- There's no risk of overflow here, since we only ever increment the total
    -- steps by 1 and then check this condition.
    when (unbudgetedStepsTotal >= ?cekSlippage) spendAccumulatedBudget
