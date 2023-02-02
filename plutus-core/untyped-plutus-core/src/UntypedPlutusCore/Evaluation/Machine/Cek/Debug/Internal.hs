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
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE UndecidableInstances  #-}

module UntypedPlutusCore.Evaluation.Machine.Cek.Debug.Internal
    ( CekState (..)
    , Context (..)
    , contextAnn
    , ioToCekM
    , cekMToIO
    , lenContext
    , cekStateContext
    , cekStateAnn
    , runCekDeBruijn
    , computeCek
    , returnCek
    , handleStep
    , defaultSlippage
    , module UntypedPlutusCore.Evaluation.Machine.Cek.Internal
    )
where

import PlutusCore.Builtin
import PlutusCore.DeBruijn
import PlutusCore.Evaluation.Machine.ExBudget
import PlutusCore.Evaluation.Machine.Exception
import PlutusCore.Evaluation.Machine.MachineParameters
import PlutusCore.Evaluation.Result
import PlutusPrelude
import UntypedPlutusCore.Core
import UntypedPlutusCore.Evaluation.Machine.Cek.CekMachineCosts (CekMachineCosts (..))

import Control.Lens hiding (Context, ix)
import Control.Monad
import Control.Monad.Except
import Control.Monad.ST
import Data.RandomAccessList.Class qualified as Env
import Data.Semigroup (stimes)
import Data.Text (Text)
import Data.Word64Array.Word8 hiding (Index)
import GHC.IO (ioToST)

{- Note [Debuggable vs Original versions of CEK]

The debuggable version of CEK was created from copying over the original CEK/Internal.hs module
and modifying the `computeCek`, `returnCek` functions.
These functions were modified so as to execute a single step (Compute or Return resp.) and immediately
return with the CEK's machine new state (`CekState`), whereas previously these two functions would iteratively run to completion.

The interface otherwise remains the same. Moreover, the `Original.runCekDeBruijn` and `Debug.runCekDeBruijn` must behave equivalently.
-}
import UntypedPlutusCore.Evaluation.Machine.Cek.Internal hiding (Context (..), runCekDeBruijn)

data CekState uni fun ann =
    -- loaded a term but not fired the cek yet
    Starting (Term NamedDeBruijn uni fun ann)
    -- the next state is computing
    | Computing WordArray (Context uni fun ann) (CekValEnv uni fun ann) (Term NamedDeBruijn uni fun ann)
    -- the next state is returning
    | Returning WordArray (Context uni fun ann) (CekValue uni fun ann)
    -- evaluation finished
    | Terminating (Term NamedDeBruijn uni fun ())

instance Pretty (CekState uni fun ann) where
    pretty = \case
        Starting{}    -> "Starting"
        Computing{}   -> "Computing"
        Returning{}   -> "Returning"
        Terminating{} -> "Terminating"

data Context uni fun ann
    = FrameApplyFun ann !(CekValue uni fun ann) !(Context uni fun ann)                         -- ^ @[V _]@
    | FrameApplyArg ann !(CekValEnv uni fun ann) !(Term NamedDeBruijn uni fun ann) !(Context uni fun ann) -- ^ @[_ N]@
    | FrameForce ann !(Context uni fun ann)                                               -- ^ @(force _)@
    | NoFrame
    deriving stock (Show)

computeCek
    :: forall uni fun ann s
    . (PrettyUni uni fun, GivenCekReqs uni fun ann s)
    => WordArray
    -> Context uni fun ann
    -> CekValEnv uni fun ann
    -> Term NamedDeBruijn uni fun ann
    -> CekM uni fun s (CekState uni fun ann)
-- s ; ρ ▻ {L A}  ↦ s , {_ A} ; ρ ▻ L
computeCek !unbudgetedSteps !ctx !env (Var _ varName) = do
    !unbudgetedSteps' <- stepAndMaybeSpend BVar unbudgetedSteps
    val <- lookupVarName varName env
    pure $ Returning unbudgetedSteps' ctx val
computeCek !unbudgetedSteps !ctx !_ (Constant _ val) = do
    !unbudgetedSteps' <- stepAndMaybeSpend BConst unbudgetedSteps
    pure $ Returning unbudgetedSteps' ctx (VCon val)
computeCek !unbudgetedSteps !ctx !env (LamAbs _ name body) = do
    !unbudgetedSteps' <- stepAndMaybeSpend BLamAbs unbudgetedSteps
    pure $ Returning unbudgetedSteps' ctx (VLamAbs name body env)
computeCek !unbudgetedSteps !ctx !env (Delay _ body) = do
    !unbudgetedSteps' <- stepAndMaybeSpend BDelay unbudgetedSteps
    pure $ Returning unbudgetedSteps' ctx (VDelay body env)
-- s ; ρ ▻ lam x L  ↦  s ◅ lam x (L , ρ)
computeCek !unbudgetedSteps !ctx !env (Force _ body) = do
    !unbudgetedSteps' <- stepAndMaybeSpend BForce unbudgetedSteps
    pure $ Computing unbudgetedSteps' (FrameForce (termAnn body) ctx) env body
-- s ; ρ ▻ [L M]  ↦  s , [_ (M,ρ)]  ; ρ ▻ L
computeCek !unbudgetedSteps !ctx !env (Apply _ fun arg) = do
    !unbudgetedSteps' <- stepAndMaybeSpend BApply unbudgetedSteps
    pure $ Computing unbudgetedSteps' (FrameApplyArg (termAnn fun) env arg ctx) env fun
-- s ; ρ ▻ abs α L  ↦  s ◅ abs α (L , ρ)
-- s ; ρ ▻ con c  ↦  s ◅ con c
-- s ; ρ ▻ builtin bn  ↦  s ◅ builtin bn arity arity [] [] ρ
computeCek !unbudgetedSteps !ctx !_ (Builtin _ bn) = do
    !unbudgetedSteps' <- stepAndMaybeSpend BBuiltin unbudgetedSteps
    let meaning = lookupBuiltin bn ?cekRuntime
    -- 'Builtin' is fully discharged.
    pure $ Returning unbudgetedSteps' ctx (VBuiltin bn (Builtin () bn) meaning)
-- s ; ρ ▻ error A  ↦  <> A
computeCek !_ !_ !_ (Error _) =
    throwing_ _EvaluationFailure

returnCek
    :: forall uni fun ann s
    . (PrettyUni uni fun, GivenCekReqs uni fun ann s)
    => WordArray
    -> Context uni fun ann
    -> CekValue uni fun ann
    -> CekM uni fun s (CekState uni fun ann)
--- Instantiate all the free variable of the resulting term in case there are any.
-- . ◅ V           ↦  [] V
returnCek !unbudgetedSteps NoFrame val = do
    spendAccumulatedBudget unbudgetedSteps
    pure $ Terminating (dischargeCekValue val)
-- s , {_ A} ◅ abs α M  ↦  s ; ρ ▻ M [ α / A ]*
returnCek !unbudgetedSteps (FrameForce _ ctx) fun = forceEvaluate unbudgetedSteps ctx fun
-- s , [_ (M,ρ)] ◅ V  ↦  s , [V _] ; ρ ▻ M
returnCek !unbudgetedSteps (FrameApplyArg _funAnn argVarEnv arg ctx) fun =
    -- MAYBE: perhaps it is worth here to merge the _funAnn with argAnn
    pure $ Computing unbudgetedSteps (FrameApplyFun (termAnn arg) fun ctx) argVarEnv arg
-- s , [(lam x (M,ρ)) _] ◅ V  ↦  s ; ρ [ x  ↦  V ] ▻ M
-- FIXME: add rule for VBuiltin once it's in the specification.
returnCek !unbudgetedSteps (FrameApplyFun _ fun ctx) arg =
    applyEvaluate unbudgetedSteps ctx fun arg

-- | @force@ a term and proceed.
-- If v is a delay then compute the body of v;
-- if v is a builtin application then check that it's expecting a type argument,
-- and either calculate the builtin application or stick a 'Force' on top of its 'Term'
-- representation depending on whether the application is saturated or not,
-- if v is anything else, fail.
forceEvaluate
    :: forall uni fun ann s
    . (PrettyUni uni fun, GivenCekReqs uni fun ann s)
    => WordArray
    -> Context uni fun ann
    -> CekValue uni fun ann
    -> CekM uni fun s (CekState uni fun ann)
forceEvaluate !unbudgetedSteps !ctx (VDelay body env) =
    pure $ Computing unbudgetedSteps ctx env body
forceEvaluate !unbudgetedSteps !ctx (VBuiltin fun term runtime) = do
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
            pure $ Returning unbudgetedSteps ctx res
        _ ->
            throwingWithCause _MachineError BuiltinTermArgumentExpectedMachineError (Just term')
forceEvaluate !_ !_ val =
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
    . (PrettyUni uni fun, GivenCekReqs uni fun ann s)
    => WordArray
    -> Context uni fun ann
    -> CekValue uni fun ann   -- lhs of application
    -> CekValue uni fun ann   -- rhs of application
    -> CekM uni fun s (CekState uni fun ann)
applyEvaluate !unbudgetedSteps !ctx (VLamAbs _ body env) arg =
    pure $ Computing unbudgetedSteps ctx (Env.cons arg env) body
-- Annotating @f@ and @exF@ with bangs gave us some speed-up, but only until we added a bang to
-- 'VCon'. After that the bangs here were making things a tiny bit slower and so we removed them.
applyEvaluate !unbudgetedSteps !ctx (VBuiltin fun term runtime) arg = do
    let argTerm = dischargeCekValue arg
        -- @term@ and @argTerm@ are fully discharged, and so @term'@ is, hence we can put it
        -- in a 'VBuiltin'.
        term' = Apply (termAnn term) term argTerm
    case runtime of
        -- It's only possible to apply a builtin application if the builtin expects a term
        -- argument next.
        BuiltinExpectArgument f -> do
            res <- evalBuiltinApp fun term' $ f arg
            pure $ Returning unbudgetedSteps ctx res
        _ ->
            throwingWithCause _MachineError UnexpectedBuiltinTermArgumentMachineError (Just term')
applyEvaluate !_ !_ val _ =
    throwingDischarged _MachineError NonFunctionalApplicationMachineError val

-- MAYBE: runCekDeBruijn can be shared between original&debug ceks by passing a `enterComputeCek` func.
runCekDeBruijn
    :: (PrettyUni uni fun)
    => MachineParameters CekMachineCosts fun (CekValue uni fun ann)
    -> ExBudgetMode cost uni fun
    -> EmitterMode uni fun
    -> Term NamedDeBruijn uni fun ann
    -> (Either (CekEvaluationException NamedDeBruijn uni fun) (Term NamedDeBruijn uni fun ()), cost, [Text])
runCekDeBruijn params mode emitMode term =
    runCekM params mode emitMode $ do
        spendBudgetCek BStartup (cekStartupCost ?cekCosts)
        enterComputeCek NoFrame Env.empty term

-- See Note [Compilation peculiarities].
-- | The entering point to the CEK machine's engine.
enterComputeCek
    :: forall uni fun ann s
    . (PrettyUni uni fun, GivenCekReqs uni fun ann s)
    => Context uni fun ann
    -> CekValEnv uni fun ann
    -> Term NamedDeBruijn uni fun ann
    -> CekM uni fun s (Term NamedDeBruijn uni fun ())
enterComputeCek ctx env term = iterToFinalState $ Computing (toWordArray 0) ctx env term
 where
   iterToFinalState :: CekState uni fun ann -> CekM uni fun s (Term NamedDeBruijn uni fun ())
   iterToFinalState = handleStep
                      >=>
                      \case
                          Terminating t -> pure t
                          x             -> iterToFinalState x

-- | The state transition function of the machine.
handleStep :: forall uni fun ann s.
             (PrettyUni uni fun, GivenCekReqs uni fun ann s)
           => CekState uni fun ann
           -> CekM uni fun s (CekState uni fun ann)
handleStep = \case
    Starting term                           ->  pure $ Computing (toWordArray 0) NoFrame Env.empty term
    Computing !unbudgetedSteps ctx env term -> computeCek unbudgetedSteps ctx env term
    Returning !unbudgetedSteps ctx val      -> returnCek unbudgetedSteps ctx val
    self@(Terminating _)                    -> pure self -- FINAL STATE, idempotent

-- * Helpers
------------

ioToCekM :: IO a -> CekM uni fun RealWorld a
ioToCekM = CekM . ioToST

cekMToIO :: CekM uni fun RealWorld a -> IO a
cekMToIO = stToIO . unCekM

cekStateContext :: Traversal' (CekState uni fun ann) (Context uni fun ann)
cekStateContext f = \case
    Computing w k e t -> (\k' -> Computing w k' e t) <$> f k
    Returning w k v   -> Returning w `flip` v <$> f k
    x                 -> pure x

cekStateAnn :: CekState uni fun ann -> Maybe ann
cekStateAnn = \case
    Computing _ _ _ t -> pure $ termAnn t
    Returning _ ctx _ -> contextAnn ctx
    Terminating{}     -> empty
    Starting t        -> pure $ termAnn t -- TODO: not sure if we want the annotation here

contextAnn :: Context uni fun ann -> Maybe ann
contextAnn = \case
    FrameApplyFun ann _ _   -> pure ann
    FrameApplyArg ann _ _ _ -> pure ann
    FrameForce ann _        -> pure ann
    NoFrame                 -> empty

lenContext :: Context uni fun ann -> Word
lenContext = go 0
    where
      go :: Word -> Context uni fun ann -> Word
      go !n = \case
              FrameApplyFun _ _ k   -> go (n+1) k
              FrameApplyArg _ _ _ k -> go (n+1) k
              FrameForce _ k        -> go (n+1) k
              NoFrame               -> 0


-- * Duplicated functions from Cek.Internal module
-- FIXME: share these functions with Cek.Internal
-- preliminary testing shows that sharing slows down original cek

-- | A 'MonadError' version of 'try'.
tryError :: MonadError e m => m a -> m (Either e a)
tryError a = (Right <$> a) `catchError` (pure . Left)

cekStepCost :: CekMachineCosts -> StepKind -> ExBudget
cekStepCost costs = \case
    BConst   -> cekConstCost costs
    BVar     -> cekVarCost costs
    BLamAbs  -> cekLamCost costs
    BApply   -> cekApplyCost costs
    BDelay   -> cekDelayCost costs
    BForce   -> cekForceCost costs
    BBuiltin -> cekBuiltinCost costs

-- | Call 'dischargeCekValue' over the received 'CekVal' and feed the resulting 'Term' to
-- 'throwingWithCause' as the cause of the failure.
throwingDischarged
    :: PrettyUni uni fun
    => AReview (EvaluationError CekUserError (MachineError fun)) t
    -> t
    -> CekValue uni fun ann
    -> CekM uni fun s x
throwingDischarged l t = throwingWithCause l t . Just . dischargeCekValue

-- See Note [Cost slippage]
-- | The default number of slippage (in machine steps) to allow.
defaultSlippage :: Slippage
defaultSlippage = 200

runCekM
    :: forall a cost uni fun ann.
    (PrettyUni uni fun)
    => MachineParameters CekMachineCosts fun (CekValue uni fun ann)
    -> ExBudgetMode cost uni fun
    -> EmitterMode uni fun
    -> (forall s. GivenCekReqs uni fun ann s => CekM uni fun s a)
    -> (Either (CekEvaluationException NamedDeBruijn uni fun) a, cost, [Text])
runCekM (MachineParameters costs runtime) (ExBudgetMode getExBudgetInfo) (EmitterMode getEmitterMode) a = runST $ do
    ExBudgetInfo{_exBudgetModeSpender, _exBudgetModeGetFinal, _exBudgetModeGetCumulative} <- getExBudgetInfo
    CekEmitterInfo{_cekEmitterInfoEmit, _cekEmitterInfoGetFinal} <- getEmitterMode _exBudgetModeGetCumulative
    let ?cekRuntime = runtime
        ?cekEmitter = _cekEmitterInfoEmit
        ?cekBudgetSpender = _exBudgetModeSpender
        ?cekCosts = costs
        ?cekSlippage = defaultSlippage
    errOrRes <- unCekM $ tryError a
    st <- _exBudgetModeGetFinal
    logs <- _cekEmitterInfoGetFinal
    pure (errOrRes, st, logs)

-- | Look up a variable name in the environment.
lookupVarName :: forall uni fun ann s . (PrettyUni uni fun) => NamedDeBruijn -> CekValEnv uni fun ann -> CekM uni fun s (CekValue uni fun ann)
lookupVarName varName@(NamedDeBruijn _ varIx) varEnv =
    case varEnv `Env.indexOne` coerce varIx of
        Nothing  -> throwingWithCause _MachineError OpenTermEvaluatedMachineError $ Just var where
            var = Var () varName
        Just val -> pure val

-- | Take pieces of a possibly partial builtin application and either create a 'CekValue' using
-- 'makeKnown' or a partial builtin application depending on whether the built-in function is
-- fully saturated or not.
evalBuiltinApp
    :: (GivenCekReqs uni fun ann s, PrettyUni uni fun)
    => fun
    -> Term NamedDeBruijn uni fun ()
    -> BuiltinRuntime (CekValue uni fun ann)
    -> CekM uni fun s (CekValue uni fun ann)
evalBuiltinApp fun term runtime = case runtime of
    BuiltinResult cost getX -> do
        spendBudgetCek (BBuiltinApp fun) cost
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
spendAccumulatedBudget :: (GivenCekReqs uni fun ann s) => WordArray -> CekM uni fun s ()
spendAccumulatedBudget !unbudgetedSteps = iforWordArray unbudgetedSteps spend
  where
    -- Making this a definition of its own causes it to inline better than actually writing it inline, for
    -- some reason.
    -- Skip index 7, that's the total counter!
    -- See Note [Structure of the step counter]
    {-# INLINE spend #-}
    spend !i !w = unless (i == 7) $ let kind = toEnum i in spendBudgetCek (BStep kind) (stimes w (cekStepCost ?cekCosts kind))

-- | Accumulate a step, and maybe spend the budget that has accumulated for a number of machine steps, but only if we've exceeded our slippage.
--
stepAndMaybeSpend :: (GivenCekReqs uni fun ann s) => StepKind -> WordArray -> CekM uni fun s WordArray
stepAndMaybeSpend !kind !unbudgetedSteps = do
    -- See Note [Structure of the step counter]
    -- This generates let-expressions in GHC Core, however all of them bind unboxed things and
    -- so they don't survive further compilation, see https://stackoverflow.com/a/14090277
    let !ix = fromIntegral $ fromEnum kind
        !unbudgetedSteps' = overIndex 7 (+1) $ overIndex ix (+1) unbudgetedSteps
        !unbudgetedStepsTotal = readArray unbudgetedSteps' 7
    -- There's no risk of overflow here, since we only ever increment the total
    -- steps by 1 and then check this condition.
    if unbudgetedStepsTotal >= ?cekSlippage
    then spendAccumulatedBudget unbudgetedSteps' >> pure (toWordArray 0)
    else pure unbudgetedSteps'
