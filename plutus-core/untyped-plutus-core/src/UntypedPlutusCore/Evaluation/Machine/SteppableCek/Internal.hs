-- editorconfig-checker-disable-file
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NPlusKPatterns #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

{-| The CEK machine.
The CEK machine relies on variables having non-equal 'Unique's whenever they have non-equal
string names. I.e. 'Unique's are used instead of string names. This is for efficiency reasons.
The CEK machines handles name capture by design. -}
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
  , mkCekTrans
  , CekTrans
  , nilSlippage
  , module UntypedPlutusCore.Evaluation.Machine.Cek.Internal
  )
where

import PlutusCore.Builtin
import PlutusCore.DeBruijn
import PlutusCore.Evaluation.Machine.ExBudget
import PlutusCore.Evaluation.Machine.ExBudgetStream
import PlutusCore.Evaluation.Machine.Exception
import PlutusCore.Evaluation.Machine.MachineParameters
import PlutusCore.Evaluation.Result
import PlutusPrelude
import UntypedPlutusCore.Core
import UntypedPlutusCore.Evaluation.Machine.Cek.CekMachineCosts
  ( CekMachineCosts
  , CekMachineCostsBase (..)
  )
import UntypedPlutusCore.Evaluation.Machine.Cek.Internal hiding (Context (..), runCekDeBruijn)
import UntypedPlutusCore.Evaluation.Machine.Cek.StepCounter

import Control.Lens hiding (Context, children)
import Control.Monad
import Control.Monad.Except (throwError)
import Control.Monad.Primitive
import Data.Proxy
import Data.RandomAccessList.Class qualified as Env
import Data.RandomAccessList.SkewBinary qualified as Env
import Data.Semigroup (stimes)
import Data.Text (Text)
import Data.Vector qualified as V
import GHC.TypeNats
import Universe

{- Note [Debuggable vs Original versions of CEK]

The debuggable version of CEK was created from copying over the original CEK/Internal.hs module
and modifying the `computeCek`, `returnCek` functions.
These functions were modified so as to execute a single step (Compute or Return resp.) and immediately
return with the CEK's machine new state (`CekState`), whereas previously these two functions would iteratively run to completion.

The interface otherwise remains the same. Moreover, the `Original.runCekDeBruijn` and `Debug.runCekDeBruijn` must behave equivalently.
-}

data CekState uni fun pat ann
  = -- loaded a term but not fired the cek yet
    Starting (NTerm uni fun pat ann)
  | -- the next state is computing
    Computing (Context uni fun pat ann) (CekValEnv uni fun pat ann) (NTerm uni fun pat ann)
  | -- the next state is returning
    Returning (Context uni fun pat ann) (CekValue uni fun pat ann)
  | -- evaluation finished
    Terminating (DischargeResult uni fun pat)

instance Pretty (CekState uni fun pat ann) where
  pretty = \case
    Starting {} -> "Starting"
    Computing {} -> "Computing"
    Returning {} -> "Returning"
    Terminating {} -> "Terminating"

-- | Similar to 'Cek.Internal.Context', but augmented with an 'ann'
data Context uni fun pat ann
  = -- | @[V _]@
    FrameAwaitArg ann !(CekValue uni fun pat ann) !(Context uni fun pat ann)
  | -- | @[_ N]@
    FrameAwaitFunTerm
      ann
      !(CekValEnv uni fun pat ann)
      !(NTerm uni fun pat ann)
      !(Context uni fun pat ann)
  | FrameAwaitFunConN ann !(Spine (Some (ValueOf uni))) !(Context uni fun pat ann)
  | FrameAwaitFunValueN ann !(ArgStackNonEmpty uni fun pat ann) !(Context uni fun pat ann)
  | -- | @(force _)@
    FrameForce ann !(Context uni fun pat ann)
  | FrameConstr
      ann
      !(CekValEnv uni fun pat ann)
      {-# UNPACK #-} !Word64
      ![NTerm uni fun pat ann]
      !(ArgStack uni fun pat ann)
      !(Context uni fun pat ann)
  | FrameCases
      ann
      !(CekValEnv uni fun pat ann)
      !(V.Vector (NTerm uni fun pat ann))
      !(Context uni fun pat ann)
  | FrameMatches
      ann
      !(CekValEnv uni fun pat ann)
      !(V.Vector (pat, NTerm uni fun pat ann))
      !(Context uni fun pat ann)
  | NoFrame

deriving stock instance
  (GShow uni, Everywhere uni Show, Show fun, Show pat, Show ann, Closed uni)
  => Show (Context uni fun pat ann)

computeCek
  :: forall uni fun pat ann s
   . (ThrowableBuiltins uni fun, Pretty pat, Typeable pat, GivenCekReqs uni fun pat ann s)
  => Context uni fun pat ann
  -> CekValEnv uni fun pat ann
  -> NTerm uni fun pat ann
  -> CekM uni fun pat s (CekState uni fun pat ann)
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
  pure $ Computing (FrameForce (getAnn body) ctx) env body
-- s ; ρ ▻ [L M]  ↦  s , [_ (M,ρ)]  ; ρ ▻ L
computeCek !ctx !env (Apply _ fun arg) = do
  stepAndMaybeSpend BApply
  pure $ Computing (FrameAwaitFunTerm (getAnn fun) env arg ctx) env fun
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
  pure $ case es of
    (t : rest) -> Computing (FrameConstr ann env i rest NilStack ctx) env t
    [] -> Returning ctx $ VConstr i EmptyStack
-- s ; ρ ▻ case S C0 ... Cn  ↦  s , case _ (C0 ... Cn, ρ) ; ρ ▻ S
computeCek !ctx !env (Case ann scrut cs) = do
  stepAndMaybeSpend BCase
  pure $ Computing (FrameCases ann env cs ctx) env scrut
computeCek !ctx !env (Match ann scrut alternatives) = do
  stepAndMaybeSpend BMatch
  pure $ Computing (FrameMatches ann env alternatives ctx) env scrut
-- s ; ρ ▻ error A  ↦  <> A
computeCek !_ !_ (Error _) =
  throwErrorWithCause (OperationalError CekEvaluationFailure) (Error ())

returnCek
  :: forall uni fun pat ann s
   . (ThrowableBuiltins uni fun, Pretty pat, Typeable pat, GivenCekReqs uni fun pat ann s)
  => Context uni fun pat ann
  -> CekValue uni fun pat ann
  -> CekM uni fun pat s (CekState uni fun pat ann)
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
  pure $ Computing (FrameAwaitArg (getAnn arg) fun ctx) argVarEnv arg
-- s , [(lam x (M,ρ)) _] ◅ V  ↦  s ; ρ [ x  ↦  V ] ▻ M
-- FIXME (https://github.com/IntersectMBO/plutus-private/issues/1878):
-- add rule for VBuiltin once it's in the specification.
returnCek (FrameAwaitArg _ fun ctx) arg =
  applyEvaluate ctx fun arg
-- Apply the constant spine exposed by an implicit builtin Case or Match branch.
returnCek (FrameAwaitFunConN ann args ctx) fun =
  case fun of
    VLamAbs {} -> applyConstant
    VBuiltin {} -> applyConstant
    -- The implicit application did not inspect the handler, so recursively discharging a
    -- constructor-shaped handler merely to populate the cause would be unbudgeted work.
    _ -> do
      spendAccumulatedBudget
      throwError $
        ErrorWithCause (StructuralError NonFunctionalApplicationMachineError) Nothing
  where
    applyConstant =
      case args of
        SpineLast arg -> applyEvaluate ctx fun (VCon arg)
        SpineCons arg rest -> applyEvaluate (FrameAwaitFunConN ann rest ctx) fun (VCon arg)
-- s , [_ V1 .. Vn] ◅ lam x (M,ρ)  ↦  s , [_ V2 .. Vn]; ρ [ x  ↦  V1 ] ▻ M
returnCek (FrameAwaitFunValueN ann args ctx) fun =
  case args of
    LastStackNonEmpty arg ->
      applyEvaluate ctx fun arg
    ConsStackNonEmpty arg rest ->
      applyEvaluate (FrameAwaitFunValueN ann rest ctx) fun arg
-- s , constr I V0 ... Vj-1 _ (Tj+1 ... Tn, ρ) ◅ Vj  ↦  s , constr i V0 ... Vj _ (Tj+2... Tn, ρ)  ; ρ ▻ Tj+1
returnCek (FrameConstr ann env i todo done ctx) e = do
  case todo of
    (next : todo') ->
      pure $ Computing (FrameConstr ann env i todo' (ConsStack e done) ctx) env next
    [] ->
      let go acc NilStack = acc
          go acc (ConsStack x xs) = go (ConsStackNonEmpty x acc) xs
       in pure $ Returning ctx $ VConstr i (MultiStack $ go (LastStackNonEmpty e) done)
-- s , case _ (C0 ... CN, ρ) ◅ constr i V1 .. Vm  ↦  s , [_ V1 ... Vm] ; ρ ▻ Ci
returnCek (FrameCases ann env cs ctx) e = case e of
  -- If the index is larger than the max bound of an Int, or negative, then it's a bad index
  -- As it happens, this will currently never trigger, since i is a Word64, and the largest
  -- Word64 value wraps to -1 as an Int64. So you can't wrap around enough to get an
  -- "apparently good" value.
  (VConstr i _)
    | fromIntegral @_ @Integer i > fromIntegral @Int @Integer maxBound ->
        throwErrorDischarged (StructuralError $ MissingCaseBranchMachineError i) e
  (VConstr i args) -> case (V.!?) cs (fromIntegral i) of
    Just t ->
      case args of
        EmptyStack -> computeCek ctx env t
        MultiStack rest -> computeCek (FrameAwaitFunValueN ann rest ctx) env t
    Nothing -> throwErrorDischarged (StructuralError $ MissingCaseBranchMachineError i) e
  VCon val -> case unCaserBuiltin ?cekCaserBuiltin val cs of
    HeadError err -> throwErrorDischarged (OperationalError $ CekCaseBuiltinError err) e
    HeadOnly fX -> pure $ Computing ctx env fX
    HeadSpine f xs -> pure $ Computing (FrameAwaitFunConN ann xs ctx) env f
  _ -> throwErrorDischarged (StructuralError NonConstrScrutinizedMachineError) e
returnCek (FrameMatches ann env alternatives ctx) scrutinee =
  enterMatchAlternatives ann ctx env alternatives scrutinee

{-| @force@ a term and proceed.
If v is a delay then compute the body of v;
if v is a builtin application then check that it's expecting a type argument,
and either calculate the builtin application or stick a 'Force' on top of its 'Term'
representation depending on whether the application is saturated or not,
if v is anything else, fail. -}
forceEvaluate
  :: forall uni fun pat ann s
   . (ThrowableBuiltins uni fun, Pretty pat, Typeable pat, GivenCekReqs uni fun pat ann s)
  => Context uni fun pat ann
  -> CekValue uni fun pat ann
  -> CekM uni fun pat s (CekState uni fun pat ann)
forceEvaluate !ctx (VDelay body env) =
  pure $ Computing ctx env body
forceEvaluate !ctx (VBuiltin fun term runtime) = do
  -- @term@ is fully discharged, and so @term'@ is, hence we can put it in a 'VBuiltin'.
  let term' = Force () term
  case runtime of
    -- It's only possible to force a builtin application if the builtin expects a type
    -- argument next.
    BuiltinExpectForce runtime' -> do
      -- We allow a type argument to appear last in the type of a built-in function,
      -- otherwise we could just assemble a 'VBuiltin' without trying to evaluate the
      -- application.
      evalBuiltinApp ctx fun term' runtime'
    _ ->
      throwErrorWithCause (StructuralError BuiltinTermArgumentExpectedMachineError) term'
forceEvaluate !_ val =
  throwErrorDischarged (StructuralError NonPolymorphicInstantiationMachineError) val

{-| Apply a function to an argument and proceed.
If the function is a lambda 'lam x ty body' then extend the environment with a binding of @v@
to x@ and call 'computeCek' on the body.
If the function is a builtin application then check that it's expecting a term argument,
and either calculate the builtin application or stick a 'Apply' on top of its 'Term'
representation depending on whether the application is saturated or not.
If v is anything else, fail. -}
applyEvaluate
  :: forall uni fun pat ann s
   . (ThrowableBuiltins uni fun, Pretty pat, Typeable pat, GivenCekReqs uni fun pat ann s)
  => Context uni fun pat ann
  -> CekValue uni fun pat ann -- lhs of application
  -> CekValue uni fun pat ann -- rhs of application
  -> CekM uni fun pat s (CekState uni fun pat ann)
applyEvaluate !ctx (VLamAbs _ body env) arg =
  pure $ Computing ctx (Env.cons arg env) body
-- Annotating @f@ and @exF@ with bangs gave us some speed-up, but only until we added a bang to
-- 'VCon'. After that the bangs here were making things a tiny bit slower and so we removed them.
applyEvaluate !ctx (VBuiltin fun term runtime) arg = do
  let argTerm = dischargeResultToTerm $ dischargeCekValue arg
      -- @term@ and @argTerm@ are fully discharged, and so @term'@ is, hence we can put it
      -- in a 'VBuiltin'.
      term' = Apply () term argTerm
  case runtime of
    -- It's only possible to apply a builtin application if the builtin expects a term
    -- argument next.
    BuiltinExpectArgument f -> evalBuiltinApp ctx fun term' $ f arg
    _ ->
      throwErrorWithCause (StructuralError UnexpectedBuiltinTermArgumentMachineError) term'
applyEvaluate !_ val _ =
  throwErrorDischarged (StructuralError NonFunctionalApplicationMachineError) val

patternFailure
  :: ( ThrowableBuiltins uni fun
     , Pretty pat
     , Typeable pat
     )
  => Text
  -> CekM uni fun pat s a
patternFailure err = do
  -- Keep the debugger path identical to the production CEK and avoid lazily discharging an
  -- arbitrarily deep scrutinee if the operational error is subsequently rendered.
  throwError $ ErrorWithCause (OperationalError $ CekPatternMatchError err) Nothing

enterMatchAlternatives
  :: (ThrowableBuiltins uni fun, Pretty pat, Typeable pat, GivenCekReqs uni fun pat ann s)
  => ann
  -> Context uni fun pat ann
  -> CekValEnv uni fun pat ann
  -> V.Vector (pat, NTerm uni fun pat ann)
  -> CekValue uni fun pat ann
  -> CekM uni fun pat s (CekState uni fun pat ann)
enterMatchAlternatives ann ctx env alternatives scrutinee = do
  -- Pattern work is spent without slippage. Flush ordinary CEK work once so subsequent matcher
  -- spends are direct affordability barriers. A reached-capture spend intentionally reserves its
  -- later spine materialization and implicit handler application.
  spendAccumulatedBudget
  case scrutinee of
    VCon con ->
      ( CekM $
          runPatternMatchM
            (unMatchBuiltin ?cekMatcherBuiltin con alternatives)
            (\work -> unCekM $ spendPattern work)
      )
        >>= enterSelected
    _ -> patternFailure "match scrutinee is not a built-in value"
  where
    !patternCost = runIdentity $ cekPatternCost ?cekCosts
    !patternStructuralCost = runIdentity $ cekPatternStructuralCost ?cekCosts
    !patternFailureCost = runIdentity $ cekPatternFailureCost ?cekCosts
    !spendPattern = \case
      PatternWork units -> case units of
        0 -> pure ()
        1 -> spendBudget BPattern patternCost
        _ -> spendBudget BPattern (stimes (toInteger units) patternCost)
      PatternStructuralWork -> spendBudget BPattern patternStructuralCost
      PatternFailureWork -> spendBudget BPattern patternFailureCost

    enterSelected = \case
      HeadError err -> patternFailure err
      HeadOnly selectedHandler -> computeCek ctx env selectedHandler
      HeadSpine selectedHandler captures ->
        computeCek (FrameAwaitFunConN ann captures ctx) env selectedHandler

-- MAYBE: runCekDeBruijn can be shared between original&debug ceks by passing a `enterComputeCek` func.
runCekDeBruijn
  :: (ThrowableBuiltins uni fun, Pretty pat, Typeable pat)
  => MachineParameters CekMachineCosts fun (CekValue uni fun pat ann) pat
  -> ExBudgetMode cost uni fun pat
  -> EmitterMode uni fun pat
  -> NTerm uni fun pat ann
  -> CekReport cost NamedDeBruijn uni fun pat
runCekDeBruijn params mode emitMode term =
  runCekM params mode emitMode $ do
    spendBudget BStartup $ runIdentity $ cekStartupCost ?cekCosts
    enterComputeCek NoFrame Env.empty term

-- See Note [Compilation peculiarities].
-- | The entering point to the CEK machine's engine.
enterComputeCek
  :: forall uni fun pat ann s
   . (ThrowableBuiltins uni fun, Pretty pat, Typeable pat, GivenCekReqs uni fun pat ann s)
  => Context uni fun pat ann
  -> CekValEnv uni fun pat ann
  -> NTerm uni fun pat ann
  -> CekM uni fun pat s (DischargeResult uni fun pat)
enterComputeCek ctx env term = iterToFinalState $ Computing ctx env term
  where
    iterToFinalState
      :: CekState uni fun pat ann -> CekM uni fun pat s (DischargeResult uni fun pat)
    iterToFinalState =
      cekTrans
        >=> \case
          Terminating t -> pure t
          x -> iterToFinalState x

{-| A CEK parameter that turns the slippage optimization *off*.

This is needed in the case of the debugger, where the accounting/budgeting costs
must be *live* updated. -}
nilSlippage :: Slippage
-- Setting the slippage to 1 would also work and turn off slippage optimization.
nilSlippage = 0

-- the type of our state transition function, `s -> m s` , aka `Kleisli m a a`
type Trans m state = state -> m state
type CekTrans uni fun pat ann s = Trans (CekM uni fun pat s) (CekState uni fun pat ann)

-- | The state transition function of the machine.
cekTrans
  :: forall uni fun pat ann s
   . (ThrowableBuiltins uni fun, Pretty pat, Typeable pat, GivenCekReqs uni fun pat ann s)
  => CekTrans uni fun pat ann s
cekTrans = \case
  Starting term -> pure $ Computing NoFrame Env.empty term
  Computing ctx env term -> computeCek ctx env term
  Returning ctx val -> returnCek ctx val
  self@Terminating {} -> pure self -- FINAL STATE, idempotent

{-| Based on the supplied arguments, initialize the CEK environment and
construct a state transition function.
Returns the constructed transition function paired with the methods to live access the running budget. -}
mkCekTrans
  :: forall cost uni fun pat ann m s
   . ( ThrowableBuiltins uni fun
     , Pretty pat
     , Typeable pat
     , PrimMonad m
     , s ~ PrimState m -- the outer monad that initializes the transition function
     )
  => MachineParameters CekMachineCosts fun (CekValue uni fun pat ann) pat
  -> ExBudgetMode cost uni fun pat
  -> EmitterMode uni fun pat
  -> Slippage
  -> m (CekTrans uni fun pat ann s, ExBudgetInfo cost uni fun pat s)
mkCekTrans
  (MachineParameters caser matcher (MachineVariantParameters costs runtime))
  (ExBudgetMode getExBudgetInfo)
  (EmitterMode getEmitterMode)
  slippage = do
    exBudgetInfo@ExBudgetInfo {_exBudgetModeSpender, _exBudgetModeGetCumulative} <-
      liftPrim getExBudgetInfo
    CekEmitterInfo {_cekEmitterInfoEmit} <- liftPrim $ getEmitterMode _exBudgetModeGetCumulative
    ctr <- newCounter (Proxy @CounterSize)
    let ?cekRuntime = runtime
        ?cekCaserBuiltin = caser
        ?cekMatcherBuiltin = matcher
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
liftCek :: (PrimMonad m, PrimState m ~ s) => CekM uni fun pat s a -> m a
liftCek = liftPrim . unCekM

cekStateContext :: Traversal' (CekState uni fun pat ann) (Context uni fun pat ann)
cekStateContext f = \case
  Computing k e t -> Computing <$> f k <*> pure e <*> pure t
  Returning k v -> Returning <$> f k <*> pure v
  x -> pure x

cekStateAnn :: CekState uni fun pat ann -> Maybe ann
cekStateAnn = \case
  Computing _ _ t -> pure $ getAnn t
  Returning ctx _ -> contextAnn ctx
  _ -> empty

contextAnn :: Context uni fun pat ann -> Maybe ann
contextAnn = \case
  FrameAwaitArg ann _ _ -> pure ann
  FrameAwaitFunTerm ann _ _ _ -> pure ann
  FrameAwaitFunConN ann _ _ -> pure ann
  FrameAwaitFunValueN ann _ _ -> pure ann
  FrameForce ann _ -> pure ann
  FrameConstr ann _ _ _ _ _ -> pure ann
  FrameCases ann _ _ _ -> pure ann
  FrameMatches ann _ _ _ -> pure ann
  NoFrame -> empty

lenContext :: Context uni fun pat ann -> Word
lenContext = go 0
  where
    go :: Word -> Context uni fun pat ann -> Word
    go !n = \case
      FrameAwaitArg _ _ k -> go (n + 1) k
      FrameAwaitFunTerm _ _ _ k -> go (n + 1) k
      FrameAwaitFunConN _ _ k -> go (n + 1) k
      FrameAwaitFunValueN _ _ k -> go (n + 1) k
      FrameForce _ k -> go (n + 1) k
      FrameConstr _ _ _ _ _ k -> go (n + 1) k
      FrameCases _ _ _ k -> go (n + 1) k
      FrameMatches _ _ _ k -> go (n + 1) k
      NoFrame -> 0

-- * Duplicated functions from Cek.Internal module

-- FIXME (https://github.com/IntersectMBO/plutus-private/issues/1879):
-- share these functions with Cek.Internal
-- preliminary testing shows that sharing slows down original cek

cekStepCost :: CekMachineCosts -> StepKind -> ExBudget
cekStepCost costs =
  runIdentity . \case
    BConst -> cekConstCost costs
    BVar -> cekVarCost costs
    BLamAbs -> cekLamCost costs
    BApply -> cekApplyCost costs
    BDelay -> cekDelayCost costs
    BForce -> cekForceCost costs
    BBuiltin -> cekBuiltinCost costs
    BConstr -> cekConstrCost costs
    BCase -> cekCaseCost costs
    BMatch -> cekMatchCost costs

{-| Call 'dischargeCekValue' over the received 'CekVal' and feed the resulting 'Term' to
'throwErrorWithCause' as the cause of the failure. -}
throwErrorDischarged
  :: (ThrowableBuiltins uni fun, Pretty pat, Typeable pat)
  => EvaluationError (MachineError fun) CekUserError
  -> CekValue uni fun pat ann
  -> CekM uni fun pat s x
throwErrorDischarged err = throwErrorWithCause err . dischargeResultToTerm . dischargeCekValue

-- | Look up a variable name in the environment.
lookupVarName
  :: forall uni fun pat ann s
   . (ThrowableBuiltins uni fun, Pretty pat, Typeable pat)
  => NamedDeBruijn
  -> CekValEnv uni fun pat ann
  -> CekM uni fun pat s (CekValue uni fun pat ann)
lookupVarName varName@(NamedDeBruijn _ varIx) varEnv =
  Env.contIndexOne
    (throwErrorWithCause (StructuralError OpenTermEvaluatedMachineError) $ Var () varName)
    pure
    varEnv
    (coerce varIx)

{-| Take a possibly partial builtin application and

- either create a 'CekValue' by evaluating the application if it's saturated (emitting logs, if
   any, along the way), potentially failing evaluation
- or create a partial builtin application otherwise

and proceed with the returning phase of the CEK machine. -}
evalBuiltinApp
  :: (ThrowableBuiltins uni fun, Pretty pat, Typeable pat, GivenCekReqs uni fun pat ann s)
  => Context uni fun pat ann
  -> fun
  -> NTerm uni fun pat ()
  -> BuiltinRuntime (CekValue uni fun pat ann)
  -> CekM uni fun pat s (CekState uni fun pat ann)
evalBuiltinApp ctx fun term runtime = case runtime of
  BuiltinCostedResult budgets0 getFXs -> do
    let exCat = BBuiltinApp fun
        spendBudgets (ExBudgetLast budget) = spendBudget exCat budget
        spendBudgets (ExBudgetCons budget budgets) =
          spendBudget exCat budget *> spendBudgets budgets
    spendBudgets budgets0
    case getFXs of
      BuiltinSuccess y ->
        returnCek ctx y
      BuiltinSuccessWithLogs logs y -> do
        ?cekEmitter logs
        returnCek ctx y
      BuiltinFailure logs err -> do
        ?cekEmitter logs
        throwBuiltinErrorWithCause term err
  _ -> returnCek ctx $ VBuiltin fun term runtime
{-# INLINE evalBuiltinApp #-}

spendBudget
  :: GivenCekSpender uni fun pat s
  => ExBudgetCategory fun
  -> ExBudget
  -> CekM uni fun pat s ()
spendBudget = unCekBudgetSpender ?cekBudgetSpender

-- | Spend the budget that has been accumulated for a number of machine steps.
spendAccumulatedBudget :: GivenCekReqs uni fun pat ann s => CekM uni fun pat s ()
spendAccumulatedBudget = do
  let ctr = ?cekStepCounter
  iforCounter_ ctr spend
  resetCounter ctr
  where
    -- Making this a definition of its own causes it to inline better than actually writing it inline, for
    -- some reason.
    -- Fixed Match steps are accumulated like other machine steps but retain the public
    -- 'BPattern' category. Matcher work is spent directly through its supplied spending function.
    -- See Note [Structure of the step counter]
    {-# INLINE spend #-}
    spend !i !w =
      if i == totalCountIndex
        then pure ()
        else
          let kind = toEnum i
           in case kind of
                BMatch ->
                  when (w /= 0) $ spendBudget BPattern $ stimes w (cekStepCost ?cekCosts kind)
                _ -> spendBudget (BStep kind) $ stimes w (cekStepCost ?cekCosts kind)
      where
        totalCountIndex = fromIntegral $ natVal $ Proxy @TotalCountIndex

{-| Accumulate a non-pattern step, and maybe spend the budget that has accumulated for a number
of machine steps, but only if we've exceeded our slippage. Pattern steps are direct-spent. -}
stepAndMaybeSpend :: GivenCekReqs uni fun pat ann s => StepKind -> CekM uni fun pat s ()
stepAndMaybeSpend !kind = do
  -- See Note [Structure of the step counter]
  -- This generates let-expressions in GHC Core, however all of them bind unboxed things and
  -- so they don't survive further compilation, see https://stackoverflow.com/a/14090277
  let !counterIndex = fromEnum kind
      ctr = ?cekStepCounter
      !totalStepIndex = fromIntegral $ natVal (Proxy @TotalCountIndex)
  !unbudgetedStepsTotal <- modifyCounter totalStepIndex (+ 1) ctr
  _ <- modifyCounter counterIndex (+ 1) ctr
  -- There's no risk of overflow here, since we only ever increment the total
  -- steps by 1 and then check this condition.
  when (unbudgetedStepsTotal >= ?cekSlippage) spendAccumulatedBudget
