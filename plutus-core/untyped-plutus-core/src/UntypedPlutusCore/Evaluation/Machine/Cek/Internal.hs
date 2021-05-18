-- | The CEK machine.
-- The CEK machine relies on variables having non-equal 'Unique's whenever they have non-equal
-- string names. I.e. 'Unique's are used instead of string names. This is for efficiency reasons.
-- The CEK machines handles name capture by design.

{-# LANGUAGE ConstraintKinds          #-}
{-# LANGUAGE DataKinds                #-}
{-# LANGUAGE DeriveAnyClass           #-}
{-# LANGUAGE FlexibleInstances        #-}
{-# LANGUAGE ImplicitParams           #-}
{-# LANGUAGE LambdaCase               #-}
{-# LANGUAGE MultiParamTypeClasses    #-}
{-# LANGUAGE NPlusKPatterns           #-}
{-# LANGUAGE OverloadedStrings        #-}
{-# LANGUAGE RankNTypes               #-}
{-# LANGUAGE ScopedTypeVariables      #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TypeApplications         #-}
{-# LANGUAGE TypeFamilies             #-}
{-# LANGUAGE TypeOperators            #-}
{-# LANGUAGE UndecidableInstances     #-}

module UntypedPlutusCore.Evaluation.Machine.Cek.Internal
    -- See Note [Compilation peculiarities].
    ( EvaluationResult(..)
    , CekValue(..)
    , CekUserError(..)
    , CekEvaluationException
    , CekBudgetSpender(..)
    , ExBudgetInfo(..)
    , ExBudgetMode(..)
    , CekCarryingM (..)
    , CekM
    , ErrorWithCause(..)
    , EvaluationError(..)
    , ExBudgetCategory(..)
    , PrettyUni
    , extractEvaluationResult
    , runCek
    )
where

import           ErrorCode
import           PlutusPrelude

import           UntypedPlutusCore.Core
import           UntypedPlutusCore.Subst

import           PlutusCore.Constant
import           PlutusCore.Evaluation.Machine.ExBudget
import           PlutusCore.Evaluation.Machine.ExMemory
import           PlutusCore.Evaluation.Machine.Exception
import           PlutusCore.Evaluation.Result
import           PlutusCore.Name
import           PlutusCore.Pretty
import           PlutusCore.Universe
import           UntypedPlutusCore.Evaluation.Machine.Cek.CekMachineCosts (CekMachineCosts (..))

import           Control.Lens                                             (ix, (^?))
import           Control.Lens.Review
import           Control.Monad.Catch
import           Control.Monad.Except
import           Control.Monad.ST
import           Control.Monad.ST.Unsafe
import           Data.Array
import           Data.DList                                               (DList)
import qualified Data.DList                                               as DList
import           Data.Hashable                                            (Hashable)
import qualified Data.Kind                                                as GHC
import           Data.Proxy
import           Data.STRef
import           Data.Text.Prettyprint.Doc

{- Note [Compilation peculiarities]
READ THIS BEFORE TOUCHING ANYTHING IN THIS FILE

Don't use @StrictData@, it makes the machine slower by several percent.

Exporting the 'computeCek' function from this module causes the CEK machine to become slower by
up to 25%. I repeat: just adding 'computeCek' to the export list makes the evaluator substantially
slower. The reason for this is that with 'computeCek' exported the generated GHC Core is much worse:
it contains more lambdas, allocates more stuff etc. While perhaps surprising, this is not an
unusual behavior of the compiler as https://wiki.haskell.org/Performance/GHC explains:

> Indeed, generally speaking GHC will inline across modules just as much as it does within modules,
> with a single large exception. If GHC sees that a function 'f' is called just once, it inlines it
> regardless of how big 'f' is. But once 'f' is exported, GHC can never see that it's called exactly
> once, even if that later turns out to be the case. This inline-once optimisation is pretty
> important in practice.
>
> So: if you care about performance, do not export functions that are not used outside the module
> (i.e. use an explicit export list, and keep it as small as possible).

Now clearly 'computeCek' cannot be inlined in 'runCek' whether it's exported or not, since
'computeCek' is recursive. However:

1. GHC is _usually_ smart enough to perform the worker/wrapper transformation and inline the wrapper
   (however experiments have shown that sticking the internals of the CEK machine, budgeting modes
   and the API into the same file prevents GHC from performing the worker/wrapper transformation for
   some reason likely related to "we've been compiling this for too long, let's leave it at that"
2. GHC seems to be able to massage the definition of 'computeCek' into something more performant
   making use of knowing exactly how 'computeCek' is used, essentially tailoring the definition of
   'computeCek' for a particular invocation in 'runCek'

Hence we don't export 'computeCek' and instead define 'runCek' in this file and export it, even
though the rest of the user-facing API (which 'runCek' is a part of) is defined downstream.

Another problem is handling mutual recursion in the 'computeCek'/'returnCek'/'forceEvaluate'/etc
family. If we keep these functions at the top level, GHC won't be able to pull the constraints out of
the family (confirmed by inspecting Core: GHC thinks that since the superclass constraints
populating the dictionary representing the @Ix fun@ constraint are redundant, they can be replaced
with calls to 'error' in a recursive call, but that changes the dictionary and so it can no longer
be pulled out of recursion). But that entails passing a redundant argument around, which slows down
the machine a tiny little bit.

Hence we define a number of the functions as local functions making use of a
shared context from their parent function. This also allows GHC to inline almost
all of the machine into a single definition (with a bunch of recursive join
points in it).

In general, it's advised to run benchmarks (and look at Core output if the results are suspicious)
on any changes in this file.
-}

{- Note [Scoping]
The CEK machine does not rely on the global uniqueness condition, so the renamer pass is not a
prerequisite. The CEK machine correctly handles name shadowing.
-}

data ExBudgetCategory fun
    = BConst
    | BVar
    | BLamAbs
    | BApply
    | BDelay
    | BForce
    | BError
    | BBuiltin         -- Cost of evaluating a Builtin AST node
    | BBuiltinApp fun  -- Cost of evaluating a fully applied builtin function
    | BStartup
    deriving stock (Show, Eq, Ord, Generic)
    deriving anyclass (NFData, Hashable)
instance Show fun => Pretty (ExBudgetCategory fun) where
    pretty = viaShow

instance ExBudgetBuiltin fun (ExBudgetCategory fun) where
    exBudgetBuiltin = BBuiltinApp

type TermWithMem uni fun = Term Name uni fun ExMemory

{- Note [Arities in VBuiltin]
The VBuiltin value below contains two copies of the arity (list of
TypeArg/TermArg pairs) for the relevant builtin.  The second of these
is consumed as the builtin is instantiated and applied to arguments,
to check that type and term arguments are interleaved correctly.  The
first copy of the arity is left unaltered and only used by
dischargeCekValue if we have to convert the frame back into a term
(see mkBuiltinApplication).  An alternative would be to look up the
full arity in mkBuiltinApplication, but that would require a lot of
things to be monadic (including the PrettyBy instance for CekValue,
which is a problem.)
-}

data BuiltinApp uni fun = BuiltinApp
    { _builtinAppTerm    :: TermWithMem uni fun  -- Must be lazy!
    , _builtinAppRuntime :: !(BuiltinRuntime (CekValue uni fun))
    }

instance (GShow uni, Closed uni, uni `Everywhere` Show, Show fun) => Show (BuiltinApp uni fun) where
    show (BuiltinApp term _) = show term

instance (GEq uni, Closed uni, uni `Everywhere` Eq, Eq fun) => Eq (BuiltinApp uni fun) where
    BuiltinApp term1 _ == BuiltinApp term2 _ = term1 == term2

-- 'Values' for the modified CEK machine.
data CekValue uni fun =
    VCon ExMemory (Some (ValueOf uni))
  | VDelay ExMemory (TermWithMem uni fun) (CekValEnv uni fun)
  | VLamAbs ExMemory Name (TermWithMem uni fun) (CekValEnv uni fun)
  | VBuiltin            -- A partial builtin application, accumulating arguments for eventual full application.
      ExMemory
      fun
      (BuiltinApp uni fun)
    deriving (Show, Eq) -- Eq is just for tests.

type CekValEnv uni fun = UniqueMap TermUnique (CekValue uni fun)

-- | The CEK machine is parameterized over a @spendBudget@ function that has (roughly) the same type
-- as the one from the 'SpendBudget' class (and so the @SpendBudget@ instance for 'CekM'
-- defers to the function stored in the environment). This makes the budgeting machinery extensible
-- and allows us to separate budgeting logic from evaluation logic and avoid branching on the union
-- of all possible budgeting state types during evaluation.
newtype CekBudgetSpender uni fun s = CekBudgetSpender
    { unCekBudgetSpender :: ExBudgetCategory fun -> ExBudget -> CekM uni fun s ()
    }

-- General enough to be able to handle a spender having one, two or any number of 'STRef's
-- under the hood.
-- | Runtime budgeting info.
data ExBudgetInfo cost uni fun s = ExBudgetInfo
    { _exBudgetModeSpender  :: !(CekBudgetSpender uni fun s)  -- ^ A spending function.
    , _exBudgetModeGetFinal :: !(ST s cost)                   -- ^ For accessing the final state.
    }

-- We make a separate data type here just to save the caller of the CEK machine from those pesky
-- 'ST'-related details.
-- Strictly speaking the 'uni' param is unneeded, but it helps avoid places where we'd otherwise need
-- a 'Proxy' to pin down 'uni'.
-- | A budgeting mode to execute the CEK machine in.
newtype ExBudgetMode cost uni fun = ExBudgetMode
    { unExBudgetMode :: forall s. ST s (ExBudgetInfo cost uni fun s)
    }

{- Note [Implicit parameters in the machine]
The traditional way to pass context into a function is to use 'ReaderT'. However, 'ReaderT' has some
disadvantages.
- It requires threading through the context even where you don't need it (every monadic bind)
- It *can* often be optimized away, but this requires GHC to be somewhat clever and do a lot of
  case-of-case to lift all the arguments out.

Moreover, if your context is global (i.e. constant across the lifetime of the monad, i.e. you don't
need 'local'), then you're buying some extra power (the ability to pass in a different context somewhere
deep inside the computation) which you don't need.

There are three main alternatives:
- Explicit function parameters. Simple, doesn't get tied up in the Monad operations, *does* still
present the appearance of letting you do 'local'. But a bit cluttered.
- Implicit parameters. A bit esoteric, can be bundled up into a constraint synonym and just piped to
where they're needed, essentially the same as explicit parameters in terms of runtime.
- Constraints via 'reflection'. Quite esoteric, *does* get you global parameters (within their scope),
bit of a hassle threading around all the extra type parameters.

We're using implicit parameters for now, which seems to strike a good balance of speed and convenience.
I haven't tried 'reflection' in detail, but I believe the main thing it would do is to make the parameters
global - but we already have this for most of the hot functions by making them all local definitions, so
they don't actually take the context as an argument even at the source level.
-}

-- | Implicit parameter for the builtin runtime.
type GivenCekRuntime uni fun = (?cekRuntime :: (BuiltinsRuntime fun (CekValue uni fun)))
-- | Implicit parameter for the log emitter reference.
type GivenCekEmitter s = (?cekEmitter :: (Maybe (STRef s (DList String))))
-- | Implicit parameter for budget spender.
type GivenCekSpender uni fun s = (?cekBudgetSpender :: (CekBudgetSpender uni fun s))
-- | Constraint requiring all of the machine's implicit parameters.
type GivenCekReqs uni fun s = (GivenCekRuntime uni fun, GivenCekEmitter s, GivenCekSpender uni fun s)

data CekUserError
    = CekOutOfExError ExRestrictingBudget -- ^ The final overspent (i.e. negative) budget.
    | CekEvaluationFailure -- ^ Error has been called or a builtin application has failed
    deriving (Show, Eq, Generic, NFData)

instance HasErrorCode CekUserError where
    errorCode CekEvaluationFailure {} = ErrorCode 37
    errorCode CekOutOfExError {}      = ErrorCode 36

{- Note [Being generic over 'term' in errors]
Our error for the CEK machine carries a term with it as a possible 'cause'. This is defined in
terms of an underlying type that is generic over this 'term' type.

The point is that in many different cases we can annotate an evaluation failure with a 'Term' that
caused it. Originally we were using 'CekValue' instead of 'Term', however that meant that we had to
ignore some important cases where we just can't produce a 'CekValue', for example if we encounter
a free variable, we can't turn it into a 'CekValue' and report the result as the cause of the
failure, which is bad. 'Term' is strictly more general than 'CekValue' and so we can always
1. report things like free variables
2. report a 'CekValue' turned into a 'Term' via 'dischargeCekValue'
We need the latter, because the constant application machinery, in the context of the CEK machine,
expects a list of 'CekValue's and so in the event of failure it has to report one of those
arguments, so we have no option but to call the constant application machinery with 'CekValue'
being the cause of a potential failure. But as mentioned, turning a 'CekValue' into a 'Term' is
no problem and we need that elsewhere anyway, so we don't need any extra machinery for calling the
constant application machinery over a list of 'CekValue's and turning the cause of a possible
failure into a 'Term', apart from the straightforward generalization of the error type.
-}

-- type CekM :: (GHC.Type -> GHC.Type) -> GHC.Type -> GHC.Type -> GHC.Type -> GHC.Type
-- -- | The monad the CEK machine runs in.
-- newtype CekM uni fun s a = CekM
--     { unCekM :: ST s a
--     } deriving newtype (Functor, Applicative, Monad)

-- -- | The CEK machine-specific 'EvaluationException'.
-- type CekEvaluationException uni fun =
--     EvaluationException CekUserError (MachineError fun (Term Name uni fun ())) (Term Name uni fun ())

type CekCarryingM :: GHC.Type -> (GHC.Type -> GHC.Type) -> GHC.Type -> GHC.Type -> GHC.Type -> GHC.Type
-- | The monad the CEK machine runs in.
newtype CekCarryingM term uni fun s a = CekCarryingM
    { unCekCarryingM :: ST s a
    } deriving newtype (Functor, Applicative, Monad)

type CekM uni fun = CekCarryingM (Term Name uni fun ()) uni fun

-- | The CEK machine-specific 'EvaluationException'.
type CekEvaluationExceptionCarrying term fun =
    EvaluationException CekUserError (MachineError fun term) term

type CekEvaluationException uni fun = CekEvaluationExceptionCarrying (Term Name uni fun ()) fun

-- | The set of constraints we need to be able to print things in universes, which we need in order to throw exceptions.
type PrettyUni uni fun = (GShow uni, Closed uni, Pretty fun, Typeable uni, Typeable fun, Everywhere uni PrettyConst)

{- Note [Throwing exceptions in ST]
This note represents MPJ's best understanding right now, might be wrong.

We use a moderately evil trick to throw exceptions in ST, but unlike the evil trick for catching them, it's hidden.

The evil is that the 'MonadThrow' instance for 'ST' uses 'unsafeIOToST . throwIO'! Sneaky! The author has marked it
"Trustworthy"", no less. However, I believe this to be safe for basically the same reasons as our trick to catch
exceptions is safe, see Note [Catching exceptions in ST]
-}

{- Note [Catching exceptions in ST]
This note represents MPJ's best understanding right now, might be wrong.

We use a moderately evil trick to catch exceptions in ST. This uses the unsafe ST <-> IO conversion functions to go into IO,
catch the exception, and then go back into ST.

Why is this okay? Recall that IO ~= ST RealWorld, i.e. it is just ST with a special thread token. The unsafe conversion functions
just coerce from one to the other. So the thread token remains the same, it's just that we'll potentially leak it from ST, and we don't
get ordering guarantees with other IO actions.

But in our case this is okay, because:

1. We do not leak the original ST thread token, since we only pass it into IO and then immediately back again.
2. We don't have ordering guarantees with other IO actions, but we don't care because we don't do any side effects, we only catch a single kind of exception.
3. We *do* have ordering guarantees between the throws inside the ST action and the catch, since they are ultimately using the same thread token.
-}

-- | Call 'dischargeCekValue' over the received 'CekVal' and feed the resulting 'Term' to
-- 'throwingWithCause' as the cause of the failure.
throwingDischarged
    :: (PrettyUni uni fun)
    => AReview (EvaluationError CekUserError (MachineError fun (Term Name uni fun ()))) t -> t -> CekValue uni fun -> CekM uni fun s x
throwingDischarged l t = throwingWithCause l t . Just . void . dischargeCekValue

withErrorDischarging
    :: CekCarryingM (CekValue uni fun) uni fun s a
    -> CekCarryingM (Term Name uni fun ()) uni fun s a
withErrorDischarging = coerce

instance PrettyUni uni fun => MonadError (CekEvaluationException uni fun) (CekM uni fun s) where
    throwError = CekCarryingM . throwM
    catchError = error "Not supposed to be called"

instance PrettyUni uni fun =>
            MonadError
                (CekEvaluationExceptionCarrying (CekValue uni fun) fun)
                (CekCarryingM (CekValue uni fun) uni fun s) where
    throwError = CekCarryingM . throwM . mapCauseInMachineException (void . dischargeCekValue)
    catchError = error "Not supposed to be called"

-- instance GivenCekEmitter s => MonadEmitter (CekM uni fun s) where
--     emit = emitCek

instance AsEvaluationFailure CekUserError where
    _EvaluationFailure = _EvaluationFailureVia CekEvaluationFailure

instance Pretty CekUserError where
    pretty (CekOutOfExError (ExRestrictingBudget res)) =
        group $ "The budget was overspent. Final negative state:" <+> pretty res
    pretty CekEvaluationFailure = "The provided Plutus code called 'error'."

spendBudgetCek :: GivenCekSpender uni fun s => ExBudgetCategory fun -> ExBudget -> CekM uni fun s ()
spendBudgetCek = let (CekBudgetSpender spend) = ?cekBudgetSpender in spend

emitCek :: GivenCekEmitter s => String -> CekM uni fun s ()
emitCek str =
    let mayLogsRef = ?cekEmitter
    in case mayLogsRef of
        Nothing      -> pure ()
        Just logsRef -> CekCarryingM $ modifySTRef logsRef (`DList.snoc` str)

{- | Given a possibly partially applied/instantiated builtin, reconstruct the
   original application from the type and term arguments we've got so far, using
   the supplied arity.  This also attempts to handle the case of bad
   interleavings for use in error messages.  The caller has to add the extra
   type or term argument that caused the error, then mkBuiltinApp works its way
   along the arity reconstructing the term.  When it can't find an argument of
   the appropriate kind it looks for one of the other kind (which should be the
   one supplied by the user): if it finds one it adds an extra application or
   instantiation as appropriate to what it's constructed so far and returns the
   result.  If there are no arguments of either kind left it just returns what
   it has at that point.  The only circumstances where this is currently called
   is if (a) the machine is returning a partially applied builtin, or (b) a
   wrongly interleaved builtin application is being reported in an error.  Note
   that we don't call this function if a builtin fails for some reason like
   division by zero; the term is discarded in that case anyway (see
   Note [Ignoring context in UserEvaluationError] in Exception.hs)
-}

-- see Note [Scoping].
-- | Instantiate all the free variables of a term by looking them up in an environment.
-- Mutually recursive with dischargeCekVal.
dischargeCekValEnv :: CekValEnv uni fun -> TermWithMem uni fun -> TermWithMem uni fun
dischargeCekValEnv valEnv =
    -- We recursively discharge the environments of Cek values, but we will gradually end up doing
    -- this to terms which have no free variables remaining, at which point we won't call this
    -- substitution function any more and so we will terminate.
    termSubstFreeNames $ \name -> do
        val <- lookupName name valEnv
        Just $ dischargeCekValue val

-- Convert a CekValue into a term by replacing all bound variables with the terms
-- they're bound to (which themselves have to be obtain by recursively discharging values).
dischargeCekValue :: CekValue uni fun -> TermWithMem uni fun
dischargeCekValue = \case
    VCon     ex val                  -> Constant ex val
    VDelay   ex body env             -> Delay ex (dischargeCekValEnv env body)
    VLamAbs  ex name body env        -> LamAbs ex name (dischargeCekValEnv env body)
    VBuiltin _ _ (BuiltinApp term _) -> term
    {- We only discharge a value when (a) it's being returned by the machine,
       or (b) it's needed for an error message.  When we're discharging VBuiltin
       we use arity0 to get the type and term arguments into the right sequence. -}

instance (Closed uni, GShow uni, uni `EverywhereAll` '[PrettyConst, ExMemoryUsage], Pretty fun) =>
            PrettyBy PrettyConfigPlc (CekValue uni fun) where
    prettyBy cfg = prettyBy cfg . dischargeCekValue

type instance UniOf (CekValue uni fun) = uni

instance (Closed uni, uni `Everywhere` ExMemoryUsage) => FromConstant (CekValue uni fun) where
    fromConstant val = VCon (memoryUsage val) val

instance AsConstant (CekValue uni fun) where
    asConstant (VCon _ val) = Just val
    asConstant _            = Nothing

instance ToExMemory (CekValue uni fun) where
    toExMemory = \case
        VCon     ex _     -> ex
        VDelay   ex _ _   -> ex
        VLamAbs  ex _ _ _ -> ex
        VBuiltin ex _ _   -> ex

data Frame uni fun
    = FrameApplyFun (CekValue uni fun)                         -- ^ @[V _]@
    | FrameApplyArg (CekValEnv uni fun) (TermWithMem uni fun)  -- ^ @[_ N]@
    | FrameForce                                               -- ^ @(force _)@
    deriving (Show)

type Context uni fun = [Frame uni fun]

runCekM
    :: forall a cost uni fun.
    (PrettyUni uni fun)
    => BuiltinsRuntime fun (CekValue uni fun)
    -> ExBudgetMode cost uni fun
    -> Bool
    -> (forall s. GivenCekReqs uni fun s => CekM uni fun s a)
    -> (Either (CekEvaluationException uni fun) a, cost, [String])
runCekM runtime (ExBudgetMode getExBudgetInfo) emitting a = runST $ do
    exBudgetMode <- getExBudgetInfo
    mayLogsRef <- if emitting then Just <$> newSTRef DList.empty else pure Nothing
    let ?cekRuntime = runtime
        ?cekEmitter = mayLogsRef
        ?cekBudgetSpender = _exBudgetModeSpender exBudgetMode
    errOrRes <- unsafeIOToST $ try @_ @(CekEvaluationException uni fun) $ unsafeSTToIO $ unCekCarryingM a
    st' <- _exBudgetModeGetFinal exBudgetMode
    logs <- case mayLogsRef of
        Nothing      -> pure []
        Just logsRef -> DList.toList <$> readSTRef logsRef
    pure (errOrRes, st', logs)

-- | Extend an environment with a variable name, the value the variable stands for
-- and the environment the value is defined in.
extendEnv :: Name -> CekValue uni fun -> CekValEnv uni fun -> CekValEnv uni fun
extendEnv = insertByName

-- | Look up a variable name in the environment.
lookupVarName :: forall uni fun s . (PrettyUni uni fun) => Name -> CekValEnv uni fun -> CekM uni fun s (CekValue uni fun)
lookupVarName varName varEnv = do
    case lookupName varName varEnv of
        Nothing  -> throwingWithCause _MachineError OpenTermEvaluatedMachineError $ Just var where
            var = Var () varName
        Just val -> pure val

-- | Retrieve the meaning of a built-in function.
lookupBuiltinApp
    :: forall uni fun s. (Ix fun, PrettyUni uni fun)
    => ExMemory -> fun -> BuiltinsRuntime fun (CekValue uni fun) -> CekM uni fun s (BuiltinApp uni fun)
lookupBuiltinApp mem fun (BuiltinsRuntime meanings) =
    case meanings ^? ix fun of
        Nothing      -> throwingWithCause _MachineError (UnknownBuiltin fun) Nothing
        Just meaning -> pure $ BuiltinApp (Builtin mem fun) meaning

-- | Take pieces of a 'BuiltinApp' and either create a 'Value' using 'makeKnown' or a partial
-- builtin application depending on whether the built-in function is fully saturated or not.
evalBuiltinApp
    :: (GivenCekReqs uni fun s, PrettyUni uni fun)
    => ExMemory
    -> fun
    -> TermWithMem uni fun
    -> BuiltinRuntime (CekValue uni fun)
    -> CekM uni fun s (CekValue uni fun)
evalBuiltinApp _   fun _    (BuiltinRuntime (TypeSchemeResult _) _ x cost) = do
    spendBudgetCek (BBuiltinApp fun) cost
    flip unWithEmitterT emitCek $ makeKnown x
evalBuiltinApp mem fun term runtime =
    pure . VBuiltin mem fun $ BuiltinApp term runtime
{-# INLINE evalBuiltinApp #-}

-- See Note [Builtin application evaluation].
-- | Either 'Apply' or 'Force' a (possibly partially applied) built-in function depending on
--
-- 1. what the builtin expects
-- 2. whether the 'Maybe' argument is a 'Just' or 'Nothing'
--
-- (the two answers must agree, otherwise we have an error) and invoke 'evalBuiltinApp'.
evalFeedBuiltinApp
    :: forall uni fun s. (PrettyUni uni fun, GivenCekReqs uni fun s)
    => ExMemory
    -> fun
    -> BuiltinApp uni fun
    -> Maybe (CekValue uni fun)
    -> CekM uni fun s (CekValue uni fun)
evalFeedBuiltinApp mem fun (BuiltinApp term (BuiltinRuntime sch ar f exF)) e =
    case (sch, e) of
        (TypeSchemeArrow _ schB, Just arg) -> do
            x <- withErrorDischarging $ readKnown arg
            let exF' = exF $ toExMemory arg
            evalBuiltinApp
                mem
                fun
                (Apply mem term $ dischargeCekValue arg)
                (BuiltinRuntime schB ar (f x) exF')
        (TypeSchemeAll  _ schK, Nothing) ->
            evalBuiltinApp
                mem
                fun
                (Force mem term)
                (BuiltinRuntime (schK Proxy) ar f exF)
        _ ->
            -- TODO: fixme.
            throwingWithCause _MachineError EmptyBuiltinArityMachineError Nothing

-- See Note [Compilation peculiarities].
-- | The entering point to the CEK machine's engine.
enterComputeCek
    :: forall uni fun s
    . (Ix fun, PrettyUni uni fun, GivenCekReqs uni fun s)
    => CekMachineCosts
    -> Context uni fun
    -> CekValEnv uni fun
    -> TermWithMem uni fun
    -> CekM uni fun s (Term Name uni fun ())
enterComputeCek costs = computeCek where
    -- | The computing part of the CEK machine.
    -- Either
    -- 1. adds a frame to the context and calls 'computeCek' ('Force', 'Apply')
    -- 2. calls 'returnCek' on values ('Delay', 'LamAbs', 'Constant', 'Builtin')
    -- 3. returns 'EvaluationFailure' ('Error')
    -- 4. looks up a variable in the environment and calls 'returnCek' ('Var')
    computeCek
        :: Context uni fun
        -> CekValEnv uni fun
        -> TermWithMem uni fun
        -> CekM uni fun s (Term Name uni fun ())
    -- s ; ρ ▻ {L A}  ↦ s , {_ A} ; ρ ▻ L
    computeCek ctx env (Var _ varName) = do
        spendBudgetCek BVar (cekVarCost costs)
        val <- lookupVarName varName env
        returnCek ctx val
    computeCek ctx _ (Constant ex val) = do
        spendBudgetCek BConst (cekConstCost costs)
        returnCek ctx (VCon ex val)
    computeCek ctx env (LamAbs ex name body) = do
        spendBudgetCek BLamAbs (cekLamCost costs)
        returnCek ctx (VLamAbs ex name body env)
    computeCek ctx env (Delay ex body) = do
        spendBudgetCek BDelay (cekDelayCost costs)
        returnCek ctx (VDelay ex body env)
    -- s ; ρ ▻ lam x L  ↦  s ◅ lam x (L , ρ)
    computeCek ctx env (Force _ body) = do
        spendBudgetCek BForce (cekForceCost costs)
        computeCek (FrameForce : ctx) env body
    -- s ; ρ ▻ [L M]  ↦  s , [_ (M,ρ)]  ; ρ ▻ L
    computeCek ctx env (Apply _ fun arg) = do
        spendBudgetCek BApply (cekApplyCost costs)
        computeCek (FrameApplyArg env arg : ctx) env fun
    -- s ; ρ ▻ abs α L  ↦  s ◅ abs α (L , ρ)
    -- s ; ρ ▻ con c  ↦  s ◅ con c
    -- s ; ρ ▻ builtin bn  ↦  s ◅ builtin bn arity arity [] [] ρ
    computeCek ctx _ (Builtin ex bn) = do
        spendBudgetCek BBuiltin (cekBuiltinCost costs)
        builtinApp <- lookupBuiltinApp ex bn ?cekRuntime
        returnCek ctx (VBuiltin ex bn builtinApp)
    -- s ; ρ ▻ error A  ↦  <> A
    computeCek _ _ (Error _) = do
        throwing_ _EvaluationFailure

    {- | The returning phase of the CEK machine.
    Returns 'EvaluationSuccess' in case the context is empty, otherwise pops up one frame
    from the context and uses it to decide how to proceed with the current value v.

      * 'FrameForce': call forceEvaluate
      * 'FrameApplyArg': call 'computeCek' over the context extended with 'FrameApplyFun'
      * 'FrameApplyFun': call applyEvaluate to attempt to apply the function
          stored in the frame to an argument.  If the function is a lambda 'lam x ty body'
          then extend the environment with a binding of v to x and call computeCek on the body.
          If the is a builtin application then check that it's expecting a term argument,
          and if it's the final argument then apply the builtin to its arguments
          return the result, or extend the value with the new argument and call
          returnCek.  If v is anything else, fail.
    -}
    returnCek :: Context uni fun -> CekValue uni fun -> CekM uni fun s (Term Name uni fun ())
    --- Instantiate all the free variable of the resulting term in case there are any.
    -- . ◅ V           ↦  [] V
    returnCek [] val = pure $ void $ dischargeCekValue val
    -- s , {_ A} ◅ abs α M  ↦  s ; ρ ▻ M [ α / A ]*
    returnCek (FrameForce : ctx) fun = forceEvaluate ctx fun
    -- s , [_ (M,ρ)] ◅ V  ↦  s , [V _] ; ρ ▻ M
    returnCek (FrameApplyArg argVarEnv arg : ctx) fun = do
        computeCek (FrameApplyFun fun : ctx) argVarEnv arg
    -- s , [(lam x (M,ρ)) _] ◅ V  ↦  s ; ρ [ x  ↦  V ] ▻ M
    -- FIXME: add rule for VBuiltin once it's in the specification.
    returnCek (FrameApplyFun fun : ctx) arg = do
        applyEvaluate ctx fun arg

    {- Note [Accumulating arguments].  The VBuiltin value contains lists of type and
    term arguments which grow as new arguments are encountered.  In the code below
    We just add new entries by appending to the end of the list: l -> l++[x].  This
    doesn't look terrbily good, but we don't expect the lists to ever contain more
    than three or four elements, so the cost is unlikely to be high.  We could
    accumulate lists in the normal way and reverse them when required, but this is
    error-prone and reversal adds an extra cost anyway.  We could also use something
    like Data.Sequence, but again we incur an extra cost because we have to convert
    to a normal list when passing the arguments to the constant application
    machinery.  If we really care we might want to convert the CAM to use sequences
    instead of lists.
    -}

    -- | @force@ a term and proceed.
    -- If v is a delay then compute the body of v;
    -- if v is a builtin application then check that it's expecting a type argument,
    -- either apply the builtin to its arguments and return the result,
    -- or extend the value with @force@ and call returnCek;
    -- if v is anything else, fail.
    forceEvaluate
        :: Context uni fun -> CekValue uni fun -> CekM uni fun s (Term Name uni fun ())
    forceEvaluate ctx (VDelay _ body env) = computeCek ctx env body
    forceEvaluate ctx (VBuiltin ex fun bn) = evalFeedBuiltinApp ex fun bn Nothing >>= returnCek ctx
    forceEvaluate _ val =
        throwingDischarged _MachineError NonPolymorphicInstantiationMachineError val

    -- | Apply a function to an argument and proceed.
    -- If the function is a lambda 'lam x ty body' then extend the environment with a binding of @v@
    -- to x@ and call 'computeCek' on the body.
    -- If the function is a builtin application then check that it's expecting a term argument, and if
    -- it's the final argument then apply the builtin to its arguments, return the result, or extend
    -- the value with the new argument and call 'returnCek'. If v is anything else, fail.
    applyEvaluate
        :: Context uni fun
        -> CekValue uni fun   -- lhs of application
        -> CekValue uni fun   -- rhs of application
        -> CekM uni fun s (Term Name uni fun ())
    applyEvaluate ctx (VLamAbs _ name body env) arg = computeCek ctx (extendEnv name arg env) body
    applyEvaluate ctx (VBuiltin ex fun bn) arg = evalFeedBuiltinApp ex fun bn (Just arg) >>= returnCek ctx
    applyEvaluate _ val _ =
        throwingDischarged _MachineError NonFunctionalApplicationMachineError val

-- See Note [Compilation peculiarities].
-- | Evaluate a term using the CEK machine and keep track of costing, logging is optional.
runCek
    :: ( uni `Everywhere` ExMemoryUsage, Ix fun, PrettyUni uni fun)
    => CekMachineCosts
    -> BuiltinsRuntime fun (CekValue uni fun)
    -> ExBudgetMode cost uni fun
    -> Bool
    -> Term Name uni fun ()
    -> (Either (CekEvaluationException uni fun) (Term Name uni fun ()), cost, [String])
runCek costs runtime mode emitting term =
    runCekM runtime mode emitting $ do
        spendBudgetCek BStartup (cekStartupCost costs)
        enterComputeCek costs [] mempty memTerm
  where
    memTerm = withMemory term
    {- This is a temporary workaround for a bug where every AST node was being
       annotated with the size of the entire AST, leading to the costing
       functions for builtins being supplied with incorrect sizes and producing
       inflated results.  In the longer term this should be reworked: we only
       need memory sizes for constants, and it should be possible to obtain them
       more directly.
     -}
    withMemory =
        \case
         Constant () v      -> Constant (memoryUsage v) v
         Builtin  () b      -> Builtin  1 b
         Var      () name   -> Var      1 name
         LamAbs   () name t -> LamAbs   1 name (withMemory t)
         Apply    () t1 t2  -> Apply    1 (withMemory t1) (withMemory t2)
         Delay    () t      -> Delay    1 (withMemory t)
         Force    () t      -> Force    1 (withMemory t)
         Error    ()        -> Error    1
