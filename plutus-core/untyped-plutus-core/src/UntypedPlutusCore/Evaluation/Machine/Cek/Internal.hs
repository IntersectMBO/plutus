-- | The CEK machine.
-- The CEK machine relies on variables having non-equal 'Unique's whenever they have non-equal
-- string names. I.e. 'Unique's are used instead of string names. This is for efficiency reasons.
-- The CEK machines handles name capture by design.

{-# LANGUAGE BangPatterns             #-}
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
import           PlutusCore.Evaluation.Machine.MachineParameters
import           PlutusCore.Evaluation.Result
import           PlutusCore.Name
import           PlutusCore.Pretty
import           PlutusCore.Universe
import           UntypedPlutusCore.Evaluation.Machine.Cek.CekMachineCosts (CekMachineCosts (..))

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

{- Note [Instances for BuiltinRuntime]
We need to be able to print 'CekValue's and for that we need a 'Show' instance for 'BuiltinRuntime',
but functions are not printable and hence we provide a dummy instance. Same applies to 'Eq'.

We could define

    instance Eq (BuiltinRuntime term) where
        _ == _ = True

however this is very unsafe (as two different functions can be, well, different). The reason
why

    instance Eq (BuiltinRuntime (CekValue uni fun))
        _ == _ = True

is not as unsafe is because the 'VBuiltin' constructor stores the term representation of the
partially applied builtin and so we get actual equality from there, which is why it's fine to
ignore the partially applied builtin itself.
-}

-- See Note [Instances for BuiltinRuntime].
instance Show (BuiltinRuntime (CekValue uni fun)) where
    show _ = "<builtin_runtime>"

-- See Note [Instances for BuiltinRuntime].
instance Eq (BuiltinRuntime (CekValue uni fun)) where
    _ == _ = True

-- 'Values' for the modified CEK machine.
data CekValue uni fun =
    VCon (Some (ValueOf uni))
  | VDelay (Term Name uni fun ()) (CekValEnv uni fun)
  | VLamAbs Name (Term Name uni fun ()) (CekValEnv uni fun)
  | VBuiltin            -- A partial builtin application, accumulating arguments for eventual full application.
      !fun                   -- So that we know, for what builtin we're calculating the cost.
                             -- TODO: any chance we could sneak this into 'BuiltinRuntime'
                             -- where we have a partially instantiated costing function anyway?
      (Term Name uni fun ()) -- This must be lazy. It represents the partial application of the
                             -- builtin function that we're going to run when it's fully saturated.
                             -- We need the 'Term' to be able to return it in case full saturation
                             -- is never achieved and a partial application needs to be returned
                             -- in the result. The laziness is important, because the arguments are
                             -- discharged values and discharging is expensive, so we don't want to
                             -- do it unless we really have to.
      (CekValEnv uni fun)    -- For discharging.
      !(BuiltinRuntime (CekValue uni fun))  -- The partial application and its costing function.
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

{- Note [Being generic over @term@ in 'CekM']
We have a @term@-generic version of 'CekM' called 'CekCarryingM', which itself requires a
@term@-generic version of 'CekEvaluationException' called 'CekEvaluationExceptionCarrying'.
This enables us to implement 'MonadError' instances that allow for throwing errors in both the CEK
machine and the builtin application machinery (as Note [Being generic over 'term' in errors]
explains, those are different kinds of errors) and otherwise we'd have to have more plumbing between
these two and turning the builtin application machinery's 'MonadError' constraint into an explicit
'Either' just to dispatch on it in the CEK machine and rethrow the error non-purely  (we used to
have that) has to cost some. Plus, being @term@-generic also enables us to throw actual exceptions
using the normal 'throwError', 'throwing_', 'throwingWithCause' etc business instead of duplicating
all that API for exceptions (we used to have @lookupBuiltinExc@, @throwingWithCauseExc@ etc).
-}

-- See Note [Being generic over @term@ in 'CekM'].
type CekCarryingM :: GHC.Type -> (GHC.Type -> GHC.Type) -> GHC.Type -> GHC.Type -> GHC.Type -> GHC.Type
-- | The monad the CEK machine runs in.
newtype CekCarryingM term uni fun s a = CekCarryingM
    { unCekCarryingM :: ST s a
    } deriving newtype (Functor, Applicative, Monad)

type CekM uni fun = CekCarryingM (Term Name uni fun ()) uni fun

-- | The CEK machine-specific 'EvaluationException'.
type CekEvaluationExceptionCarrying term fun =
    EvaluationException CekUserError (MachineError fun) term

type CekEvaluationException uni fun = CekEvaluationExceptionCarrying (Term Name uni fun ()) fun

-- | The set of constraints we need to be able to print things in universes, which we need in order to throw exceptions.
type PrettyUni uni fun = (GShow uni, Closed uni, Pretty fun, Typeable uni, Typeable fun, Everywhere uni PrettyConst)

{- Note [Throwing exceptions in ST]
This note represents MPJ's best understanding right now, might be wrong.

We use a moderately evil trick to throw exceptions in ST, but unlike the evil trick for catching them, it's hidden.

The evil is that the 'MonadThrow' instance for 'ST' uses 'unsafeIOToST . throwIO'! Sneaky! The author has marked it
"Trustworthy", no less. However, I believe this to be safe for basically the same reasons as our trick to catch
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
    => AReview (EvaluationError CekUserError (MachineError fun)) t
    -> t
    -> CekValue uni fun
    -> CekM uni fun s x
throwingDischarged l t = throwingWithCause l t . Just . dischargeCekValue

-- | Enable throwing 'CekValue' rather than 'Term' within the received action.
withErrorDischarging
    :: CekCarryingM (CekValue uni fun) uni fun s a
    -> CekCarryingM (Term Name uni fun ()) uni fun s a
withErrorDischarging = coerce

-- | Handle a 'CekEvaluationException' in the 'CekCarryingM' monad.
catchErrorCekCarryingM
    :: PrettyUni uni fun
    => CekCarryingM term uni fun s a
    -> (CekEvaluationException uni fun -> CekCarryingM term uni fun s a)
    -> CekCarryingM term uni fun s a
catchErrorCekCarryingM a h =
    CekCarryingM . unsafeIOToST $ unsafeRunCekCarryingM a `catch` (unsafeRunCekCarryingM . h) where
        -- | Unsafely run a 'CekCarryingM' computation in the 'IO' monad by converting the
        -- underlying 'ST' to it.
        unsafeRunCekCarryingM :: CekCarryingM term uni fun s a -> IO a
        unsafeRunCekCarryingM = unsafeSTToIO . unCekCarryingM

instance PrettyUni uni fun => MonadError (CekEvaluationException uni fun) (CekM uni fun s) where
    throwError = CekCarryingM . throwM
    catchError = catchErrorCekCarryingM

instance PrettyUni uni fun =>
            MonadError
                (CekEvaluationExceptionCarrying (CekValue uni fun) fun)
                (CekCarryingM (CekValue uni fun) uni fun s) where
    throwError = CekCarryingM . throwM . mapCauseInMachineException dischargeCekValue
    -- We don't need this function, but it doesn't hurt to define it anyway.
    a `catchError` h =
        -- We can't convert a thrown 'Term' into a 'CekValue' without computing that 'Term',
        -- which is silly, so we just lose the term that caused the failure.
        a `catchErrorCekCarryingM` \(ErrorWithCause err _) -> h $ ErrorWithCause err Nothing

-- It would be really nice to define this instance, so that we can use 'makeKnown' directly in
-- the 'CekM' monad without the 'WithEmitterT' nonsense. Unfortunately, GHC doesn't like
-- implicit params in instance contexts. As GHC's docs explain:
--
-- > Reason: exactly which implicit parameter you pick up depends on exactly where you invoke a
-- > function. But the "invocation" of instance declarations is done behind the scenes by the
-- > compiler, so it's hard to figure out exactly where it is done. The easiest thing is to outlaw
-- > the offending types.
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

-- see Note [Scoping].
-- | Instantiate all the free variables of a term by looking them up in an environment.
-- Mutually recursive with dischargeCekVal.
dischargeCekValEnv :: CekValEnv uni fun -> Term Name uni fun () -> Term Name uni fun ()
dischargeCekValEnv valEnv =
    -- We recursively discharge the environments of Cek values, but we will gradually end up doing
    -- this to terms which have no free variables remaining, at which point we won't call this
    -- substitution function any more and so we will terminate.
    termSubstFreeNames $ \name -> do
        val <- lookupName name valEnv
        Just $ dischargeCekValue val

-- | Convert a 'CekValue' into a 'Term' by replacing all bound variables with the terms
-- they're bound to (which themselves have to be obtain by recursively discharging values).
dischargeCekValue :: CekValue uni fun -> Term Name uni fun ()
dischargeCekValue = \case
    VCon     val           -> Constant () val
    VDelay   body env      -> dischargeCekValEnv env $ Delay () body
    -- 'computeCek' turns @LamAbs _ name body@ into @VLamAbs name body env@ where @env@ is an
    -- argument of 'computeCek' and hence we need to start discharging outside of the reassembled
    -- lambda, otherwise @name@ could clash with the names that we have in @env@.
    VLamAbs  name body env -> dischargeCekValEnv env $ LamAbs () name body
    -- We only discharge a value when (a) it's being returned by the machine,
    -- or (b) it's needed for an error message.
    VBuiltin _ term env _  -> dischargeCekValEnv env term

instance (Closed uni, GShow uni, uni `EverywhereAll` '[PrettyConst, ExMemoryUsage], Pretty fun) =>
            PrettyBy PrettyConfigPlc (CekValue uni fun) where
    prettyBy cfg = prettyBy cfg . dischargeCekValue

type instance UniOf (CekValue uni fun) = uni

instance FromConstant (CekValue uni fun) where
    fromConstant val = VCon val

instance AsConstant (CekValue uni fun) where
    asConstant (VCon val) = Just val
    asConstant _          = Nothing

instance (Closed uni, uni `Everywhere` ExMemoryUsage) => ToExMemory (CekValue uni fun) where
    toExMemory = \case
        VCon c      -> memoryUsage c
        VDelay {}   -> 1
        VLamAbs {}  -> 1
        VBuiltin {} -> 1

data Frame uni fun
    = FrameApplyFun (CekValue uni fun)                         -- ^ @[V _]@
    | FrameApplyArg (CekValEnv uni fun) (Term Name uni fun ()) -- ^ @[_ N]@
    | FrameForce                                               -- ^ @(force _)@
    deriving (Show)

type Context uni fun = [Frame uni fun]

-- | A 'MonadError' version of 'try'.
tryError :: MonadError e m => m a -> m (Either e a)
tryError a = (Right <$> a) `catchError` (pure . Left)

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
    errOrRes <- unCekCarryingM $ tryError a
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

-- | Take pieces of a possibly partial builtin application and either create a 'CekValue' using
-- 'makeKnown' or a partial builtin application depending on whether the built-in function is
-- fully saturated or not.
evalBuiltinApp
    :: (GivenCekReqs uni fun s, PrettyUni uni fun)
    => fun
    -> Term Name uni fun ()
    -> CekValEnv uni fun
    -> BuiltinRuntime (CekValue uni fun)
    -> CekM uni fun s (CekValue uni fun)
evalBuiltinApp fun term env runtime@(BuiltinRuntime sch x cost) = case sch of
    TypeSchemeResult _ -> do
        spendBudgetCek (BBuiltinApp fun) cost
        flip unWithEmitterT emitCek $ makeKnown x
    _ -> pure $ VBuiltin fun term env runtime
{-# INLINE evalBuiltinApp #-}

-- See Note [Compilation peculiarities].
-- | The entering point to the CEK machine's engine.
enterComputeCek
    :: forall uni fun s
    . (Ix fun, PrettyUni uni fun, GivenCekReqs uni fun s, uni `Everywhere` ExMemoryUsage)
    => CekMachineCosts
    -> Context uni fun
    -> CekValEnv uni fun
    -> Term Name uni fun ()
    -> CekM uni fun s (Term Name uni fun ())
enterComputeCek costs = computeCek where
    -- | The computing part of the CEK machine.
    -- Either
    -- 1. adds a frame to the context and calls 'computeCek' ('Force', 'Apply')
    -- 2. calls 'returnCek' on values ('Delay', 'LamAbs', 'Constant', 'Builtin')
    -- 3. throws 'EvaluationFailure' ('Error')
    -- 4. looks up a variable in the environment and calls 'returnCek' ('Var')
    computeCek
        :: Context uni fun
        -> CekValEnv uni fun
        -> Term Name uni fun ()
        -> CekM uni fun s (Term Name uni fun ())
    -- s ; ρ ▻ {L A}  ↦ s , {_ A} ; ρ ▻ L
    computeCek ctx env (Var _ varName) = do
        spendBudgetCek BVar (cekVarCost costs)
        val <- lookupVarName varName env
        returnCek ctx val
    computeCek ctx _ (Constant _ val) = do
        spendBudgetCek BConst (cekConstCost costs)
        returnCek ctx (VCon val)
    computeCek ctx env (LamAbs _ name body) = do
        spendBudgetCek BLamAbs (cekLamCost costs)
        returnCek ctx (VLamAbs name body env)
    computeCek ctx env (Delay _ body) = do
        spendBudgetCek BDelay (cekDelayCost costs)
        returnCek ctx (VDelay body env)
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
    -- s ; ρ ▻ builtin bn  ↦  s ◅ builtin bn (Builtin () bn) (runtimeOf bn) ρ
    computeCek ctx env term@(Builtin _ bn) = do
        spendBudgetCek BBuiltin (cekBuiltinCost costs)
        meaning <- lookupBuiltin bn ?cekRuntime
        returnCek ctx (VBuiltin bn term env meaning)
    -- s ; ρ ▻ error A  ↦  <> A
    computeCek _ _ (Error _) = do
        throwing_ _EvaluationFailure

    {- | The returning phase of the CEK machine.
    Returns 'EvaluationSuccess' in case the context is empty, otherwise pops up one frame
    from the context and uses it to decide how to proceed with the current value v.

      * 'FrameForce': call forceEvaluate
      * 'FrameApplyArg': call 'computeCek' over the context extended with 'FrameApplyFun'
      * 'FrameApplyFun': call 'applyEvaluate' to attempt to apply the function
          stored in the frame to an argument.
    -}
    returnCek :: Context uni fun -> CekValue uni fun -> CekM uni fun s (Term Name uni fun ())
    --- Instantiate all the free variable of the resulting term in case there are any.
    -- . ◅ V           ↦  [] V
    returnCek [] val = pure $ dischargeCekValue val
    -- s , {_ A} ◅ abs α M  ↦  s ; ρ ▻ M [ α / A ]*
    returnCek (FrameForce : ctx) fun = forceEvaluate ctx fun
    -- s , [_ (M,ρ)] ◅ V  ↦  s , [V _] ; ρ ▻ M
    returnCek (FrameApplyArg argVarEnv arg : ctx) fun = do
        computeCek (FrameApplyFun fun : ctx) argVarEnv arg
    -- s , [(lam x (M,ρ)) _] ◅ V  ↦  s ; ρ [ x  ↦  V ] ▻ M
    -- FIXME: add rule for VBuiltin once it's in the specification.
    returnCek (FrameApplyFun fun : ctx) arg = do
        applyEvaluate ctx fun arg

    -- | @force@ a term and proceed.
    -- If v is a delay then compute the body of v;
    -- if v is a builtin application then check that it's expecting a type argument,
    -- and either calculate the builtin application or stick a 'Force' on top of its 'Term'
    -- representation depending on whether the application is saturated or not,
    -- if v is anything else, fail.
    forceEvaluate
        :: Context uni fun -> CekValue uni fun -> CekM uni fun s (Term Name uni fun ())
    forceEvaluate ctx (VDelay body env) = computeCek ctx env body
    forceEvaluate ctx (VBuiltin fun term env (BuiltinRuntime sch f exF)) = do
        let term' = Force () term
        case sch of
            -- It's only possible to force a builtin application if the builtin expects a type
            -- argument next.
            TypeSchemeAll  _ schK -> do
                let runtime' = BuiltinRuntime (schK Proxy) f exF
                -- We allow a type argument to appear last in the type of a built-in function,
                -- otherwise we could just assemble a 'VBuiltin' without trying to evaluate the
                -- application.
                res <- evalBuiltinApp fun term' env runtime'
                returnCek ctx res
            _ ->
                throwingWithCause _MachineError BuiltinTermArgumentExpectedMachineError (Just term')
    forceEvaluate _ val =
        throwingDischarged _MachineError NonPolymorphicInstantiationMachineError val

    -- | Apply a function to an argument and proceed.
    -- If the function is a lambda 'lam x ty body' then extend the environment with a binding of @v@
    -- to x@ and call 'computeCek' on the body.
    -- If the function is a builtin application then check that it's expecting a term argument,
    -- and either calculate the builtin application or stick a 'Apply' on top of its 'Term'
    -- representation depending on whether the application is saturated or not.
    -- If v is anything else, fail.
    applyEvaluate
        :: Context uni fun
        -> CekValue uni fun   -- lhs of application
        -> CekValue uni fun   -- rhs of application
        -> CekM uni fun s (Term Name uni fun ())
    applyEvaluate ctx (VLamAbs name body env) arg = computeCek ctx (extendEnv name arg env) body
    -- TODO: check if annotating @f@ and @exF@ with bangs speeds anything up.
    applyEvaluate ctx (VBuiltin fun term env (BuiltinRuntime sch f exF)) arg = do
        let term' = Apply () term $ dischargeCekValue arg
        case sch of
            -- It's only possible to apply a builtin application if the builtin expects a term
            -- argument next.
            TypeSchemeArrow _ schB -> do
                -- The builtin application machinery wants to be able to throw a 'CekValue' rather
                -- than a 'Term', hence 'withErrorDischarging'.
                x <- withErrorDischarging $ readKnown arg
                -- TODO: should we bother computing that 'ExMemory' eagerly? We may not need it.
                let runtime' = BuiltinRuntime schB (f x) . exF $ toExMemory arg
                res <- evalBuiltinApp fun term' env runtime'
                returnCek ctx res
            _ ->
                throwingWithCause _MachineError UnexpectedBuiltinTermArgumentMachineError (Just term')
    applyEvaluate _ val _ =
        throwingDischarged _MachineError NonFunctionalApplicationMachineError val

-- See Note [Compilation peculiarities].
-- | Evaluate a term using the CEK machine and keep track of costing, logging is optional.
runCek
    :: ( uni `Everywhere` ExMemoryUsage, Ix fun, PrettyUni uni fun)
    => MachineParameters CekMachineCosts CekValue uni fun
    -> ExBudgetMode cost uni fun
    -> Bool
    -> Term Name uni fun ()
    -> (Either (CekEvaluationException uni fun) (Term Name uni fun ()), cost, [String])
runCek (MachineParameters cekcosts runtime) mode emitting term =
    runCekM runtime mode emitting $ do
        spendBudgetCek BStartup (cekStartupCost cekcosts)
        enterComputeCek cekcosts [] mempty term
