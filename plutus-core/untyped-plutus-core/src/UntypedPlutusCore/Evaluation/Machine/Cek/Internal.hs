-- editorconfig-checker-disable-file
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
{-# LANGUAGE NamedFieldPuns           #-}
{-# LANGUAGE OverloadedStrings        #-}
{-# LANGUAGE RankNTypes               #-}
{-# LANGUAGE ScopedTypeVariables      #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TypeApplications         #-}
{-# LANGUAGE TypeFamilies             #-}
{-# LANGUAGE TypeOperators            #-}
{-# LANGUAGE UnboxedTuples            #-}
{-# LANGUAGE UndecidableInstances     #-}

{-# OPTIONS_GHC -fno-warn-orphans #-}

module UntypedPlutusCore.Evaluation.Machine.Cek.Internal
    -- See Note [Compilation peculiarities].
    ( EvaluationResult(..)
    , CekValue(..)
    , ArgStack(..)
    , transferArgStack
    , CekUserError(..)
    , CekEvaluationException
    , CekBudgetSpender(..)
    , ExBudgetInfo(..)
    , ExBudgetMode(..)
    , CekEmitter
    , CekEmitterInfo(..)
    , EmitterMode(..)
    , CekM (..)
    , ErrorWithCause(..)
    , EvaluationError(..)
    , ExBudgetCategory(..)
    , StepKind(..)
    , ThrowableBuiltins
    , extractEvaluationResult
    , spendBudgetStreamCek
    , runCekDeBruijn
    , dischargeCekValue
    , Context (..)
    , CekValEnv
    , GivenCekReqs
    , GivenCekSpender
    , StepCounter
    , CounterSize
    , TotalCountIndex
    , Slippage
    , defaultSlippage
    , NTerm
    , runCekM
    )
where

import PlutusPrelude

import UntypedPlutusCore.Core

import Data.RandomAccessList.Class qualified as Env
import Data.RandomAccessList.SkewBinary qualified as Env
import PlutusCore.Builtin
import PlutusCore.DeBruijn
import PlutusCore.Evaluation.Machine.ExBudget
import PlutusCore.Evaluation.Machine.ExBudgetStream
import PlutusCore.Evaluation.Machine.Exception
import PlutusCore.Evaluation.Machine.ExMemoryUsage
import PlutusCore.Evaluation.Machine.MachineParameters
import PlutusCore.Evaluation.Result
import PlutusCore.Pretty

import UntypedPlutusCore.Evaluation.Machine.Cek.CekMachineCosts (CekMachineCosts,
                                                                 CekMachineCostsBase (..))
import UntypedPlutusCore.Evaluation.Machine.Cek.StepCounter

import Control.Lens ((^?))
import Control.Lens.Review
import Control.Monad (unless, when)
import Control.Monad.Catch
import Control.Monad.Except (MonadError, catchError, throwError)
import Control.Monad.Primitive (PrimMonad (..))
import Control.Monad.ST
import Control.Monad.ST.Unsafe
import Data.DList qualified as DList
import Data.Functor.Identity
import Data.Hashable (Hashable)
import Data.Kind qualified as GHC
import Data.List.Extras (wix)
import Data.Proxy
import Data.Semigroup (stimes)
import Data.Text (Text)
import Data.Word
import GHC.TypeLits
import Prettyprinter
import Universe

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

Finally, it's important to put bang patterns on any Int arguments to ensure that GHC unboxes them:
this can make a surprisingly large difference.
-}

{- Note [Scoping]
The CEK machine does not rely on the global uniqueness condition, so the renamer pass is not a
prerequisite. The CEK machine correctly handles name shadowing.
-}

-- | The 'Term's that CEK can execute must have DeBruijn binders
-- 'Name' is not necessary but we leave it here for simplicity and debuggability.
type NTerm uni fun = Term NamedDeBruijn uni fun

data StepKind
    = BConst
    | BVar
    | BLamAbs
    | BApply
    | BDelay
    | BForce
    | BBuiltin -- Cost of evaluating a Builtin AST node, not the function itself
    | BConstr
    | BCase
    deriving stock (Show, Eq, Ord, Generic, Enum, Bounded)
    deriving anyclass (NFData, Hashable)

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

data ExBudgetCategory fun
    = BStep StepKind
    | BBuiltinApp fun  -- Cost of evaluating a fully applied builtin function
    | BStartup
    deriving stock (Show, Eq, Ord, Generic)
    deriving anyclass (NFData, Hashable)
instance Show fun => Pretty (ExBudgetCategory fun) where
    pretty = viaShow

instance ExBudgetBuiltin fun (ExBudgetCategory fun) where
    exBudgetBuiltin = BBuiltinApp

{- Note [Show instance for BuiltinRuntime]
We need to be able to print 'CekValue's and for that we need a 'Show' instance for 'BuiltinRuntime',
but functions are not printable and hence we provide a dummy instance.
-}

-- See Note [Show instance for BuiltinRuntime].
instance Show (BuiltinRuntime (CekValue uni fun ann)) where
    show _ = "<builtin_runtime>"

-- | A LIFO stack of 'CekValue's, useful for recording multiple arguments which will need to
-- be pushed onto the context in reverse order.
data ArgStack uni fun ann =
  EmptyStack
  | ConsStack !(CekValue uni fun ann) !(ArgStack uni fun ann)

deriving stock instance (GShow uni, Everywhere uni Show, Show fun, Show ann, Closed uni)
    => Show (ArgStack uni fun ann)

-- 'Values' for the modified CEK machine.
data CekValue uni fun ann =
    -- This bang gave us a 1-2% speed-up at the time of writing.
    VCon !(Some (ValueOf uni))
  | VDelay !(NTerm uni fun ann) !(CekValEnv uni fun ann)
  | VLamAbs !NamedDeBruijn !(NTerm uni fun ann) !(CekValEnv uni fun ann)
    -- | A partial builtin application, accumulating arguments for eventual full application.
    -- We don't need a 'CekValEnv' here unlike in the other constructors, because 'VBuiltin'
    -- values always store their corresponding 'Term's fully discharged, see the comments at
    -- the call sites (search for 'VBuiltin').
  | VBuiltin
      !fun
      -- ^ So that we know, for what builtin we're calculating the cost. We can sneak this into
      -- 'BuiltinRuntime', so that we don't need to store it here, but somehow doing so was
      -- consistently slowing evaluation down by half a percent. Might be noise, might be not, but
      -- at least we know that removing this @fun@ is not helpful anyway. See this commit reversing
      -- the change: https://github.com/input-output-hk/plutus/pull/4778/commits/86a3e24ca3c671cc27c6f4344da2bcd14f961706
      (NTerm uni fun ())
      -- ^ This must be lazy. It represents the fully discharged partial application of the builtin
      -- function that we're going to run when it's fully saturated.  We need the 'Term' to be able
      -- to return it in case full saturation is never achieved and a partial application needs to
      -- be returned in the result. The laziness is important, because the arguments are discharged
      -- values and discharging is expensive, so we don't want to do it unless we really have
      -- to. Making this field strict resulted in a 3-4.5% slowdown at the time of writing.
      !(BuiltinRuntime (CekValue uni fun ann))
      -- ^ The partial application and its costing function.
      -- Check the docs of 'BuiltinRuntime' for details.
    -- | A constructor value, including fully computed arguments and the tag.
  | VConstr {-# UNPACK #-} !Word64 !(ArgStack uni fun ann)

deriving stock instance (GShow uni, Everywhere uni Show, Show fun, Show ann, Closed uni)
    => Show (CekValue uni fun ann)

type CekValEnv uni fun ann = Env.RAList (CekValue uni fun ann)

-- | The CEK machine is parameterized over a @spendBudget@ function. This makes the budgeting machinery extensible
-- and allows us to separate budgeting logic from evaluation logic and avoid branching on the union
-- of all possible budgeting state types during evaluation.
newtype CekBudgetSpender uni fun s = CekBudgetSpender
    { unCekBudgetSpender :: ExBudgetCategory fun -> ExBudget -> CekM uni fun s ()
    }

-- General enough to be able to handle a spender having one, two or any number of 'STRef's
-- under the hood.
-- | Runtime budgeting info.
data ExBudgetInfo cost uni fun s = ExBudgetInfo
    { _exBudgetModeSpender       :: !(CekBudgetSpender uni fun s)  -- ^ A spending function.
    , _exBudgetModeGetFinal      :: !(ST s cost) -- ^ For accessing the final state.
    , _exBudgetModeGetCumulative :: !(ST s ExBudget) -- ^ For accessing the cumulative budget.
    }

-- We make a separate data type here just to save the caller of the CEK machine from those pesky
-- 'ST'-related details.
-- | A budgeting mode to execute the CEK machine in.
newtype ExBudgetMode cost uni fun = ExBudgetMode
    { unExBudgetMode :: forall s. ST s (ExBudgetInfo cost uni fun s)
    }

{- Note [Cost slippage]
Tracking the budget usage for every step in the machine adds a lot of overhead. To reduce this,
we adopt a technique which allows some overshoot of the budget ("slippage"), but only a bounded
amount.

To do this we:
- Track all the machine steps of all kinds in an set of counters in a 'StepCounter'
- Actually "spend" the budget when we've done more than some fixed number of steps, or at the end.

This saves a *lot* of time, at the cost of potentially overshooting the budget by slippage*step_cost,
which is okay so long as we bound the slippage appropriately.

Note that we're only proposing to do this for machine steps, since it's plausible that we can track
them in an optimized way. Builtins are more complicated (and infrequent), so we can just budget them
properly when we hit them.

There are two options for how to bound the slippage:
1. As a fixed number of steps
2. As a proportion of the overall budget

Option 2 initially seems much better as a bound: if we run N scripts with an overall budget of B, then
the potential overrun from 1 is N*slippage, whereas the overrun from 2 is B*slippage. That is, 2
says we always overrun by a fraction of the total amount of time you were expecting, whereas 1 says
it depends how many scripts you run... so if I send you a lot of small scripts, I could cause a lot
of overrun.

However, it turns out (empirically) that we can pick a number for 1 that gives us most of the speedup, but such
that the maximum overrun is negligible (e.g. much smaller than the "startup cost"). So in the end
we opted for option 1, which also happens to be simpler to implement.
-}

{- Note [Structure of the step counter]
The step counter is kept in a 'MutablePrimArray', which is a fast way of storing a bunch of
mutable 'Word8's.
This suits our purposes, as we need one counter for every step type, and one for the total number.

We keep the counters for each step in the first indices, so we can index them simply by using
the 'Enum' instance of 'StepKind', and the total counter in the last index.
-}

-- | The number of step counters that we need, should be the same as the number of constructors
-- of 'StepKind'.
type NumberOfStepCounters = 9
-- | The total number of counters that we need, one extra for the total counter.
-- See Note [Structure of the step counter]
type CounterSize = NumberOfStepCounters + 1
-- | The index at which the total step counter is kept.
-- See Note [Structure of the step counter]
type TotalCountIndex = NumberOfStepCounters

type Slippage = Word8
-- See Note [Cost slippage]
-- | The default number of slippage (in machine steps) to allow.
defaultSlippage :: Slippage
defaultSlippage = 200

{- Note [DList-based emitting]
Instead of emitting log lines one by one, we have a 'DList' of them in the type of emitters
(see 'CekEmitter'). That 'DList' comes from 'Emitter' and allows the latter to be an efficient
monad for logging. We leak this implementation detail in the type of emitters, because it's the
most efficient way of doing emitting, see
https://github.com/input-output-hk/plutus/pull/4421#issuecomment-1059186586
-}

-- See Note [DList-based emitting].
-- | The CEK machine is parameterized over an emitter function, similar to 'CekBudgetSpender'.
type CekEmitter uni fun s = DList.DList Text -> CekM uni fun s ()

-- | Runtime emitter info, similar to 'ExBudgetInfo'.
data CekEmitterInfo uni fun s = CekEmitterInfo {
    _cekEmitterInfoEmit       :: !(CekEmitter uni fun s)
    , _cekEmitterInfoGetFinal :: !(ST s [Text])
    }

-- | An emitting mode to execute the CEK machine in, similar to 'ExBudgetMode'.
newtype EmitterMode uni fun = EmitterMode
    { unEmitterMode :: forall s. ST s ExBudget -> ST s (CekEmitterInfo uni fun s)
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
type GivenCekRuntime uni fun ann = (?cekRuntime :: (BuiltinsRuntime fun (CekValue uni fun ann)))
-- | Implicit parameter for the log emitter reference.
type GivenCekEmitter uni fun s = (?cekEmitter :: CekEmitter uni fun s)
-- | Implicit parameter for budget spender.
type GivenCekSpender uni fun s = (?cekBudgetSpender :: (CekBudgetSpender uni fun s))
type GivenCekSlippage = (?cekSlippage :: Slippage)
type GivenCekStepCounter s = (?cekStepCounter :: StepCounter CounterSize s)
type GivenCekCosts = (?cekCosts :: CekMachineCosts)

-- | Constraint requiring all of the machine's implicit parameters.
type GivenCekReqs uni fun ann s = (GivenCekRuntime uni fun ann, GivenCekEmitter uni fun s, GivenCekSpender uni fun s, GivenCekSlippage, GivenCekStepCounter s, GivenCekCosts)

data CekUserError
    = CekOutOfExError !ExRestrictingBudget -- ^ The final overspent (i.e. negative) budget.
    | CekEvaluationFailure -- ^ Error has been called or a builtin application has failed
    deriving stock (Show, Eq, Generic)
    deriving anyclass (NFData)

type CekM :: (GHC.Type -> GHC.Type) -> GHC.Type -> GHC.Type -> GHC.Type -> GHC.Type
-- | The monad the CEK machine runs in.
newtype CekM uni fun s a = CekM
    { unCekM :: ST s a
    } deriving newtype (Functor, Applicative, Monad, PrimMonad)

-- | The CEK machine-specific 'EvaluationException'.
type CekEvaluationException name uni fun =
    EvaluationException CekUserError (MachineError fun) (Term name uni fun ())

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
    :: ThrowableBuiltins uni fun
    => AReview (EvaluationError CekUserError (MachineError fun)) t
    -> t
    -> CekValue uni fun ann
    -> CekM uni fun s x
throwingDischarged l t = throwingWithCause l t . Just . dischargeCekValue

instance ThrowableBuiltins uni fun => MonadError (CekEvaluationException NamedDeBruijn uni fun) (CekM uni fun s) where
    -- See Note [Throwing exceptions in ST].
    throwError = CekM . throwM

    -- See Note [Catching exceptions in ST].
    a `catchError` h = CekM . unsafeIOToST $ aIO `catch` hIO where
        aIO = unsafeRunCekM a
        hIO = unsafeRunCekM . h

        -- | Unsafely run a 'CekM' computation in the 'IO' monad by converting the
        -- underlying 'ST' to it.
        unsafeRunCekM :: CekM uni fun s a -> IO a
        unsafeRunCekM = unsafeSTToIO . unCekM

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
        cat
          [ "The machine terminated part way through evaluation due to overspending the budget."
          , "The budget when the machine terminated was:"
          , pretty res
          , "Negative numbers indicate the overspent budget; note that this only indicates the budget that was needed for the next step, not to run the program to completion."
          ]
    pretty CekEvaluationFailure = "The machine terminated because of an error, either from a built-in function or from an explicit use of 'error'."

spendBudgetCek :: GivenCekSpender uni fun s => ExBudgetCategory fun -> ExBudget -> CekM uni fun s ()
spendBudgetCek = let (CekBudgetSpender spend) = ?cekBudgetSpender in spend

-- see Note [Scoping].
-- | Instantiate all the free variables of a term by looking them up in an environment.
-- Mutually recursive with dischargeCekVal.
dischargeCekValEnv :: forall uni fun ann. CekValEnv uni fun ann -> NTerm uni fun () -> NTerm uni fun ()
dischargeCekValEnv valEnv = go 0
 where
  -- The lamCnt is just a counter that measures how many lambda-abstractions
  -- we have descended in the `go` loop.
  go :: Word64 -> NTerm uni fun () -> NTerm uni fun ()
  go !lamCnt =  \case
    LamAbs ann name body -> LamAbs ann name $ go (lamCnt+1) body
    var@(Var _ (NamedDeBruijn _ ndbnIx)) -> let idx = coerce ndbnIx :: Word64  in
        if lamCnt >= idx
        -- the index n is less-than-or-equal than the number of lambdas we have descended
        -- this means that n points to a bound variable, so we don't discharge it.
        then var
        else maybe
               -- var is free, leave it alone
               var
               -- var is in the env, discharge its value
               dischargeCekValue
               -- index relative to (as seen from the point of view of) the environment
               (Env.indexOne valEnv $ idx - lamCnt)
    Apply ann fun arg    -> Apply ann (go lamCnt fun) $ go lamCnt arg
    Delay ann term       -> Delay ann $ go lamCnt term
    Force ann term       -> Force ann $ go lamCnt term
    t -> t

-- | Convert a 'CekValue' into a 'Term' by replacing all bound variables with the terms
-- they're bound to (which themselves have to be obtain by recursively discharging values).
dischargeCekValue :: CekValue uni fun ann -> NTerm uni fun ()
dischargeCekValue = \case
    VCon     val                         -> Constant () val
    VDelay   body env                    -> dischargeCekValEnv env $ Delay () (void body)
    -- 'computeCek' turns @LamAbs _ name body@ into @VLamAbs name body env@ where @env@ is an
    -- argument of 'computeCek' and hence we need to start discharging outside of the reassembled
    -- lambda, otherwise @name@ could clash with the names that we have in @env@.
    VLamAbs (NamedDeBruijn n _ix) body env ->
        -- The index on the binder is meaningless, we put `0` by convention, see 'Binder'.
        dischargeCekValEnv env $ LamAbs () (NamedDeBruijn n deBruijnInitIndex) (void body)
    -- We only return a discharged builtin application when (a) it's being returned by the machine,
    -- or (b) it's needed for an error message.
    -- @term@ is fully discharged, so we can return it directly without any further discharging.
    VBuiltin _ term _                    -> term
    VConstr i es                         -> Constr () i (fmap dischargeCekValue $ stack2list es)
      where
        stack2list = go []
        go acc EmptyStack           = acc
        go acc (ConsStack arg rest) = go (arg : acc) rest

instance (PrettyUni uni, Pretty fun) => PrettyBy PrettyConfigPlc (CekValue uni fun ann) where
    prettyBy cfg = prettyBy cfg . dischargeCekValue

type instance UniOf (CekValue uni fun ann) = uni

instance HasConstant (CekValue uni fun ann) where
    asConstant (VCon val) = pure val
    asConstant _          = throwNotAConstant

    fromConstant = VCon

{-|
The context in which the machine operates.

Morally, this is a stack of frames, but we use the "intrusive list" representation so that
we can match on context and the top frame in a single, strict pattern match.
-}
data Context uni fun ann
    = FrameAwaitArg !(CekValue uni fun ann) !(Context uni fun ann)
    -- ^ @[V _]@
    | FrameAwaitFunTerm !(CekValEnv uni fun ann) !(NTerm uni fun ann) !(Context uni fun ann)
    -- ^ @[_ N]@
    | FrameAwaitFunValue !(CekValue uni fun ann) !(Context uni fun ann)
    -- ^ @[_ V]@
    | FrameForce !(Context uni fun ann)
    -- ^ @(force _)@
    -- See Note [Accumulators for terms]
    | FrameConstr !(CekValEnv uni fun ann) {-# UNPACK #-} !Word64 ![NTerm uni fun ann] !(ArgStack uni fun ann) !(Context uni fun ann)
    -- ^ @(constr i V0 ... Vj-1 _ Nj ... Nn)@
    | FrameCases !(CekValEnv uni fun ann) ![NTerm uni fun ann] !(Context uni fun ann)
    -- ^ @(case _ C0 .. Cn)@
    | NoFrame

deriving stock instance (GShow uni, Everywhere uni Show, Show fun, Show ann, Closed uni)
    => Show (Context uni fun ann)

-- See Note [ExMemoryUsage instances for non-constants].
instance (Closed uni, uni `Everywhere` ExMemoryUsage) => ExMemoryUsage (CekValue uni fun ann) where
    memoryUsage = \case
        VCon c      -> memoryUsage c
        VDelay {}   -> singletonRose 1
        VLamAbs {}  -> singletonRose 1
        VBuiltin {} -> singletonRose 1
        VConstr {}  -> singletonRose 1
    {-# INLINE memoryUsage #-}

-- | Transfers an 'ArgStack' to a series of 'Context' frames.
transferArgStack :: ArgStack uni fun ann -> Context uni fun ann -> Context uni fun ann
transferArgStack EmptyStack c           = c
transferArgStack (ConsStack arg rest) c = transferArgStack rest (FrameAwaitFunValue arg c)

-- | A 'MonadError' version of 'try'.
--
-- TODO: remove when we switch to mtl>=2.3
tryError :: MonadError e m => m a -> m (Either e a)
tryError a = (Right <$> a) `catchError` (pure . Left)

runCekM
    :: forall a cost uni fun ann
    . ThrowableBuiltins uni fun
    => MachineParameters CekMachineCosts fun (CekValue uni fun ann)
    -> ExBudgetMode cost uni fun
    -> EmitterMode uni fun
    -> (forall s. GivenCekReqs uni fun ann s => CekM uni fun s a)
    -> (Either (CekEvaluationException NamedDeBruijn uni fun) a, cost, [Text])
runCekM (MachineParameters costs runtime) (ExBudgetMode getExBudgetInfo) (EmitterMode getEmitterMode) a = runST $ do
    ExBudgetInfo{_exBudgetModeSpender, _exBudgetModeGetFinal, _exBudgetModeGetCumulative} <- getExBudgetInfo
    CekEmitterInfo{_cekEmitterInfoEmit, _cekEmitterInfoGetFinal} <- getEmitterMode _exBudgetModeGetCumulative
    ctr <- newCounter (Proxy @CounterSize)
    let ?cekRuntime = runtime
        ?cekEmitter = _cekEmitterInfoEmit
        ?cekBudgetSpender = _exBudgetModeSpender
        ?cekCosts = costs
        ?cekSlippage = defaultSlippage
        ?cekStepCounter = ctr
    errOrRes <- unCekM $ tryError a
    st <- _exBudgetModeGetFinal
    logs <- _cekEmitterInfoGetFinal
    pure (errOrRes, st, logs)
{-# INLINE runCekM #-}

-- | Look up a variable name in the environment.
lookupVarName
    :: forall uni fun ann s
    . ThrowableBuiltins uni fun
    => NamedDeBruijn -> CekValEnv uni fun ann -> CekM uni fun s (CekValue uni fun ann)
lookupVarName varName@(NamedDeBruijn _ varIx) varEnv =
    case varEnv `Env.indexOne` coerce varIx of
        Nothing  -> throwingWithCause _MachineError OpenTermEvaluatedMachineError $ Just var where
            var = Var () varName
        Just val -> pure val

-- | Spend each budget from the given stream of budgets.
spendBudgetStreamCek
    :: GivenCekReqs uni fun ann s
    => ExBudgetCategory fun
    -> ExBudgetStream
    -> CekM uni fun s ()
spendBudgetStreamCek exCat = go where
    go (ExBudgetLast budget)         = spendBudgetCek exCat budget
    go (ExBudgetCons budget budgets) = spendBudgetCek exCat budget *> go budgets
{-# INLINE spendBudgetStreamCek #-}

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

-- See Note [Compilation peculiarities].
-- | The entering point to the CEK machine's engine.
enterComputeCek
    :: forall uni fun ann s
    . (ThrowableBuiltins uni fun, GivenCekReqs uni fun ann s)
    => Context uni fun ann
    -> CekValEnv uni fun ann
    -> NTerm uni fun ann
    -> CekM uni fun s (NTerm uni fun ())
enterComputeCek = computeCek
  where
    -- | The computing part of the CEK machine.
    -- Either
    -- 1. adds a frame to the context and calls 'computeCek' ('Force', 'Apply')
    -- 2. calls 'returnCek' on values ('Delay', 'LamAbs', 'Constant', 'Builtin')
    -- 3. throws 'EvaluationFailure' ('Error')
    -- 4. looks up a variable in the environment and calls 'returnCek' ('Var')
    computeCek
        :: Context uni fun ann
        -> CekValEnv uni fun ann
        -> NTerm uni fun ann
        -> CekM uni fun s (NTerm uni fun ())
    -- s ; ρ ▻ {L A}  ↦ s , {_ A} ; ρ ▻ L
    computeCek !ctx !env (Var _ varName) = do
        stepAndMaybeSpend BVar
        val <- lookupVarName varName env
        returnCek ctx val
    -- s ; ρ ▻ con c  ↦  s ◅ con c
    computeCek !ctx !_ (Constant _ val) = do
        stepAndMaybeSpend BConst
        returnCek ctx (VCon val)
    -- s ; ρ ▻ lam x L  ↦  s ◅ lam x (L , ρ)
    computeCek !ctx !env (LamAbs _ name body) = do
        stepAndMaybeSpend BLamAbs
        returnCek ctx (VLamAbs name body env)
    -- s ; ρ ▻ delay L  ↦  s ◅ delay (L , ρ)
    computeCek !ctx !env (Delay _ body) = do
        stepAndMaybeSpend BDelay
        returnCek ctx (VDelay body env)
    -- s ; ρ ▻ force T  ↦  s , force _ ; ρ ▻ L
    computeCek !ctx !env (Force _ body) = do
        stepAndMaybeSpend BForce
        computeCek (FrameForce ctx) env body
    -- s ; ρ ▻ [L M]  ↦  s , [_ (M,ρ)]  ; ρ ▻ L
    computeCek !ctx !env (Apply _ fun arg) = do
        stepAndMaybeSpend BApply
        computeCek (FrameAwaitFunTerm env arg ctx) env fun
    -- s ; ρ ▻ builtin bn  ↦  s ◅ builtin bn arity arity [] [] ρ
    computeCek !ctx !_ (Builtin _ bn) = do
        stepAndMaybeSpend BBuiltin
        let meaning = lookupBuiltin bn ?cekRuntime
        -- 'Builtin' is fully discharged.
        returnCek ctx (VBuiltin bn (Builtin () bn) meaning)
    -- s ; ρ ▻ constr I T0 .. Tn  ↦  s , constr I _ (T1 ... Tn, ρ) ; ρ ▻ T0
    computeCek !ctx !env (Constr _ i es) = do
        stepAndMaybeSpend BConstr
        case es of
          (t : rest) -> computeCek (FrameConstr env i rest EmptyStack ctx) env t
          []         -> returnCek ctx $ VConstr i EmptyStack
    -- s ; ρ ▻ case S C0 ... Cn  ↦  s , case _ (C0 ... Cn, ρ) ; ρ ▻ S
    computeCek !ctx !env (Case _ scrut cs) = do
        stepAndMaybeSpend BCase
        computeCek (FrameCases env cs ctx) env scrut
    -- s ; ρ ▻ error  ↦  <> A
    computeCek !_ !_ (Error _) =
        throwing_ _EvaluationFailure

    {- | The returning phase of the CEK machine.
    Returns 'EvaluationSuccess' in case the context is empty, otherwise pops up one frame
    from the context and uses it to decide how to proceed with the current value v.

      * 'FrameForce': call forceEvaluate
      * 'FrameApplyArg': call 'computeCek' over the context extended with 'FrameApplyFun'
      * 'FrameApplyFun': call 'applyEvaluate' to attempt to apply the function
          stored in the frame to an argument.
    -}
    returnCek
        :: Context uni fun ann
        -> CekValue uni fun ann
        -> CekM uni fun s (NTerm uni fun ())
    --- Instantiate all the free variable of the resulting term in case there are any.
    -- . ◅ V           ↦  [] V
    returnCek NoFrame val = do
        spendAccumulatedBudget
        pure $ dischargeCekValue val
    -- s , {_ A} ◅ abs α M  ↦  s ; ρ ▻ M [ α / A ]*
    returnCek (FrameForce ctx) fun = forceEvaluate ctx fun
    -- s , [_ (M,ρ)] ◅ V  ↦  s , [V _] ; ρ ▻ M
    returnCek (FrameAwaitFunTerm argVarEnv arg ctx) fun =
        computeCek (FrameAwaitArg fun ctx) argVarEnv arg
    -- s , [(lam x (M,ρ)) _] ◅ V  ↦  s ; ρ [ x  ↦  V ] ▻ M
    -- FIXME: add rule for VBuiltin once it's in the specification.
    returnCek (FrameAwaitArg fun ctx) arg =
        applyEvaluate ctx fun arg
    -- s , [_ V] ◅ lam x (M,ρ)  ↦  s ; ρ [ x  ↦  V ] ▻ M
    returnCek (FrameAwaitFunValue arg ctx) fun =
        applyEvaluate ctx fun arg
    -- s , constr I V0 ... Vj-1 _ (Tj+1 ... Tn, ρ) ◅ Vj  ↦  s , constr i V0 ... Vj _ (Tj+2... Tn, ρ)  ; ρ ▻ Tj+1
    returnCek (FrameConstr env i todo done ctx) e = do
        let done' = ConsStack e done
        case todo of
          (next : todo') -> computeCek (FrameConstr env i todo' done' ctx) env next
          _              -> returnCek ctx $ VConstr i done'
    -- s , case _ (C0 ... CN, ρ) ◅ constr i V1 .. Vm  ↦  s , [_ V1 ... Vm] ; ρ ▻ Ci
    returnCek (FrameCases env cs ctx) e = case e of
        (VConstr i args) -> case cs ^? wix i of
            Just t  -> computeCek (transferArgStack args ctx) env t
            Nothing -> throwingDischarged _MachineError (MissingCaseBranch i) e
        _ -> throwingDischarged _MachineError NonConstrScrutinized e

    -- | @force@ a term and proceed.
    -- If v is a delay then compute the body of v;
    -- if v is a builtin application then check that it's expecting a type argument,
    -- and either calculate the builtin application or stick a 'Force' on top of its 'Term'
    -- representation depending on whether the application is saturated or not,
    -- if v is anything else, fail.
    forceEvaluate
        :: Context uni fun ann
        -> CekValue uni fun ann
        -> CekM uni fun s (NTerm uni fun ())
    forceEvaluate !ctx (VDelay body env) = computeCek ctx env body
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
                res <- evalBuiltinApp fun term' runtime'
                returnCek ctx res
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
        :: Context uni fun ann
        -> CekValue uni fun ann   -- lhs of application
        -> CekValue uni fun ann   -- rhs of application
        -> CekM uni fun s (NTerm uni fun ())
    applyEvaluate !ctx (VLamAbs _ body env) arg =
        computeCek ctx (Env.cons arg env) body
    -- Annotating @f@ and @exF@ with bangs gave us some speed-up, but only until we added a bang to
    -- 'VCon'. After that the bangs here were making things a tiny bit slower and so we removed them.
    applyEvaluate !ctx (VBuiltin fun term runtime) arg = do
        let argTerm = dischargeCekValue arg
            -- @term@ and @argTerm@ are fully discharged, and so @term'@ is, hence we can put it
            -- in a 'VBuiltin'.
            term' = Apply () term argTerm
        case runtime of
            -- It's only possible to apply a builtin application if the builtin expects a term
            -- argument next.
            BuiltinExpectArgument f -> do
                res <- evalBuiltinApp fun term' $ f arg
                returnCek ctx res
            _ ->
                throwingWithCause _MachineError UnexpectedBuiltinTermArgumentMachineError (Just term')
    applyEvaluate !_ val _ =
        throwingDischarged _MachineError NonFunctionalApplicationMachineError val

    -- | Spend the budget that has been accumulated for a number of machine steps.
    spendAccumulatedBudget :: CekM uni fun s ()
    spendAccumulatedBudget = do
        let ctr = ?cekStepCounter
        iforCounter_ ctr spend
        resetCounter ctr

    -- Making this a definition of its own causes it to inline better than actually writing it inline, for
    -- some reason.
    -- Skip index 7, that's the total counter!
    -- See Note [Structure of the step counter]
    {-# INLINE spend #-}
    spend !i !w = unless (i == (fromIntegral $ natVal $ Proxy @TotalCountIndex)) $
      let kind = toEnum i in spendBudgetCek (BStep kind) (stimes w (cekStepCost ?cekCosts kind))

    {-# INLINE stepAndMaybeSpend #-}
    -- | Accumulate a step, and maybe spend the budget that has accumulated for a number of machine steps, but only if we've exceeded our slippage.
    stepAndMaybeSpend :: StepKind -> CekM uni fun s ()
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

-- See Note [Compilation peculiarities].
-- | Evaluate a term using the CEK machine and keep track of costing, logging is optional.
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

{- Note [Accumulators for terms]
At a couple of points in the CEK machine (notably building the arguments to a constructor value)
we need to compute a list of terms into values.

Our usual strategy is to make a frame which has an (implicit) "hole" for the value we are computing,
and which stores the other sub-parts of the term as terms or values depending on whether we've computed
them yet or not (see e.g. how applications work).

We want to do the same sort of strategy here, but it's a bit more complicated. We need a hole
"in the middle" of the list, with computed values on one side and yet-to-be-computed terms on the other.
We also very much want to avoid allocating as much as possible.

The basic structure that we end up with has three parts:
1. Use the list of sub-terms from the original term as our "todo" queue, a list is a good structure for this.
2. Use an accumulator type with fast snoc to accumulate the values as we compute them.
3. Convert the accumulator quickly into a final type that is fast to process/lookup in later.

(this process was at one point made explicit with an interface, but in the end we just inlined it all away)

We tried at least three variants of this:
1. List/MutableVector/Vector
2. List/Seq/Seq
3. List/DList/List

Suprisingly, option 3 was just as performant as the others, so we opted to go with it for simplicity.
But there may well be a faster version.
-}
