-- | The CEK machine.
-- The CEK machine relies on variables having non-equal 'Unique's whenever they have non-equal
-- string names. I.e. 'Unique's are used instead of string names. This is for efficiency reasons.
-- The CEK machines handles name capture by design.

{-# LANGUAGE ConstraintKinds       #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE DeriveAnyClass        #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NPlusKPatterns        #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE UndecidableInstances  #-}

module UntypedPlutusCore.Evaluation.Machine.Cek.Internal
    -- See Note [Compilation peculiarities].
    ( EvaluationResult(..)
    , CekValue(..)
    , CekUserError(..)
    , CekEvaluationException
    , CekBudgetSpender(..)
    , CekM
    , ExBudgetMode(..)
    , ErrorWithCause(..)
    , EvaluationError(..)
    , ExBudgetCategory(..)
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

import           Control.Lens                            (AReview)
import           Control.Monad.Except
import           Control.Monad.Morph
import           Control.Monad.Reader
import           Control.Monad.ST
import           Control.Monad.State.Strict
import           Data.Array
import           Data.DList                              (DList)
import qualified Data.DList                              as DList
import           Data.Hashable                           (Hashable)
import           Data.STRef
import           Data.Text.Prettyprint.Doc

{- Note [Compilation peculiarities]
READ THIS BEFORE TOUCHING ANYTHING IN THIS FILE

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
    | BAST
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

-- 'Values' for the modified CEK machine.
data CekValue uni fun =
    VCon ExMemory (Some (ValueOf uni))
  | VDelay ExMemory (TermWithMem uni fun) (CekValEnv uni fun)
  | VLamAbs ExMemory Name (TermWithMem uni fun) (CekValEnv uni fun)
  | VBuiltin            -- A partial builtin application, accumulating arguments for eventual full application.
      ExMemory
      fun
      Arity             -- Sorts of arguments to be provided (both types and terms): *don't change this*.
      Arity             -- A copy of the arity used for checking applications/instantiatons: see Note [Arities in VBuiltin]
      Int               -- The number of @force@s to apply to the builtin.
                        -- We need it to construct a term if the machine is returning a stuck partial application.
      [CekValue uni fun]    -- Arguments we've computed so far.
    deriving (Show, Eq) -- Eq is just for tests.

type CekValEnv uni fun = UniqueMap TermUnique (CekValue uni fun)

-- | The CEK machine is parameterized over a @spendBudget@ function that has (roughly) the same type
-- as the one from the 'SpendBudget' class (and so the @SpendBudget@ instance for 'CekCarryingM'
-- defers to the function stored in the environment). This makes the budgeting machinery extensible
-- and allows us to separate budgeting logic from evaluation logic and avoid branching on the union
-- of all possible budgeting state types during evaluation.
newtype CekBudgetSpender cost uni fun = CekBudgetSpender
    { unCekBudgetSpender
        :: forall term s. ToExMemory term
        => ExBudgetCategory fun -> ExBudget -> CekCarryingM cost term uni fun s ()
    }

-- | The environment the CEK machine runs in.
data CekEnv cost uni fun s = CekEnv
    { cekEnvRuntime          :: BuiltinsRuntime fun (CekValue uni fun)
    -- 'Nothing' means no logging. 'DList' is due to the fact that we need efficient append
    -- as we store logs as "latest go last".
    , cekEnvMayEmitRef       :: Maybe (STRef s (DList String))
    , cekEnvCekBudgetSpender :: CekBudgetSpender cost uni fun
    }

data CekUserError
    = CekOutOfExError ExRestrictingBudget -- ^ The final overspent (i.e. negative) budget.
    | CekEvaluationFailure -- ^ Error has been called or a builtin application has failed
    deriving (Show, Eq, Generic, NFData)

instance HasErrorCode CekUserError where
    errorCode CekEvaluationFailure {} = ErrorCode 37
    errorCode CekOutOfExError {}      = ErrorCode 36

{- Note [Being generic over @term@ in 'CekM']
We have a @term@-generic version of 'CekM' called 'CekCarryingM', which itself requires a
@term@-generic version of 'CekEvaluationException' called 'CekEvaluationExceptionCarrying'.
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
failure into a 'Term', apart from the straightforward generalization of 'CekM'.
-}

-- | The CEK machine-specific 'EvaluationException', parameterized over @term@.
type CekEvaluationExceptionCarrying term fun =
    EvaluationException CekUserError (MachineError fun term) term

-- See Note [Being generic over @term@ in 'CekM'].
-- | A generalized version of 'CekM' carrying a @term@.
-- 'State' is inside the 'ExceptT', so we can get it back in case of error.
-- The 'cost' parameter is for keeping track of costing in the 'StateT' monad.
type CekCarryingM cost term uni fun s =
    ReaderT (CekEnv cost uni fun s)
        (ExceptT (CekEvaluationExceptionCarrying term fun)
            (StateT cost
                (ST s)))

-- | The CEK machine-specific 'EvaluationException'.
type CekEvaluationException uni fun = CekEvaluationExceptionCarrying (Term Name uni fun ()) fun

-- | The monad the CEK machine runs in.
type CekM cost uni fun s = CekCarryingM cost (Term Name uni fun ()) uni fun s

-- | A budgeting mode to execute an evaluator in.
data ExBudgetMode cost uni fun = ExBudgetMode
    { _exBudgetModeSpender :: CekBudgetSpender cost uni fun  -- ^ A spending function.
    , _exBudgetModeInitSt  :: cost                           -- ^ An initial state.
    }

instance AsEvaluationFailure CekUserError where
    _EvaluationFailure = _EvaluationFailureVia CekEvaluationFailure

instance Pretty CekUserError where
    pretty (CekOutOfExError (ExRestrictingBudget res)) =
        group $ "The budget was overspent. Final negative state:" <+> pretty res
    pretty CekEvaluationFailure = "The provided Plutus code called 'error'."

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
mkBuiltinApplication :: ExMemory -> fun -> Arity -> Int -> [TermWithMem uni fun] -> TermWithMem uni fun
mkBuiltinApplication ex bn arity0 forces0 args0 =
  go arity0 forces0 args0 (Builtin ex bn)
    where go arity forces args term =
              case (arity, args, forces) of
                -- We've got to the end and successfully constructed the entire application
                ([], [], 0)                    -> term
                -- got an expected term argument
                (TermArg:arity', arg:args', _) -> go arity' forces args' (Apply ex term arg)
                -- term expected, type found
                (TermArg:_, [], _forces'+1)    -> Force ex term
                -- got an expected type argument
                (TypeArg:arity', _, forces'+1) -> go arity' forces' args (Force ex term)
                -- type expected, term found
                (TypeArg:_, arg:_, 0)          -> Apply ex term arg
                -- something else, including partial application
                _                              -> term

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
    VCon     ex val                     -> Constant ex val
    VDelay   ex body env                -> Delay ex (dischargeCekValEnv env body)
    VLamAbs  ex name body env           -> LamAbs ex name (dischargeCekValEnv env body)
    VBuiltin ex bn arity0 _ forces args -> mkBuiltinApplication ex bn arity0 forces (fmap dischargeCekValue args)
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
        VCon     ex _         -> ex
        VDelay   ex _ _       -> ex
        VLamAbs  ex _ _ _     -> ex
        VBuiltin ex _ _ _ _ _ -> ex

instance MonadEmitter (CekCarryingM cost term uni fun s) where
    emit str = do
        mayLogsRef <- asks cekEnvMayEmitRef
        case mayLogsRef of
            Nothing      -> pure ()
            Just logsRef -> lift . lift . lift $ modifySTRef logsRef (`DList.snoc` str)

-- We only need the @Eq fun@ constraint here and not anywhere else, because in other places we have
-- @Ix fun@ which implies @Ord fun@ which implies @Eq fun@.
instance ToExMemory term =>
            SpendBudget (CekCarryingM cost term uni fun s) fun (ExBudgetCategory fun) term where
    spendBudget key budgetToSpend = do
        CekBudgetSpender spend <- asks cekEnvCekBudgetSpender
        spend key budgetToSpend

data Frame uni fun
    = FrameApplyFun (CekValue uni fun)                         -- ^ @[V _]@
    | FrameApplyArg (CekValEnv uni fun) (TermWithMem uni fun)  -- ^ @[_ N]@
    | FrameForce                                               -- ^ @(force _)@
    deriving (Show)

type Context uni fun = [Frame uni fun]

runCekM
    :: forall a cost uni fun.
       BuiltinsRuntime fun (CekValue uni fun)
    -> ExBudgetMode cost uni fun
    -> Bool
    -> (forall s. CekM cost uni fun s a)
    -> (Either (CekEvaluationException uni fun) a, cost, [String])
runCekM runtime (ExBudgetMode spender costInit) emitting a = runST $ do
    mayLogsRef <- if emitting then Just <$> newSTRef DList.empty else pure Nothing
    (errOrRes, st') <- runStateT (runExceptT . runReaderT a $ CekEnv runtime mayLogsRef spender) costInit
    logs <- case mayLogsRef of
        Nothing      -> pure []
        Just logsRef -> DList.toList <$> readSTRef logsRef
    pure (errOrRes, st', logs)

-- | Extend an environment with a variable name, the value the variable stands for
-- and the environment the value is defined in.
extendEnv :: Name -> CekValue uni fun -> CekValEnv uni fun -> CekValEnv uni fun
extendEnv = insertByName

-- | Look up a variable name in the environment.
lookupVarName :: Name -> CekValEnv uni fun -> CekM cost uni fun s (CekValue uni fun)
lookupVarName varName varEnv = do
    case lookupName varName varEnv of
        Nothing  -> throwingWithCause _MachineError OpenTermEvaluatedMachineError $ Just var where
            var = Var () varName
        Just val -> pure val


-- We provisionally charge a unit CPU cost for AST nodes: this is just to allow
-- us to count the number of times each node type is evaluated.  We may wish to
-- change this later if it turns out that different node types have
-- significantly different costs.
astNodeCost :: ExBudget
astNodeCost = ExBudget 1 0

-- | The computing part of the CEK machine.
-- Either
-- 1. adds a frame to the context and calls 'computeCek' ('Force', 'Apply')
-- 2. calls 'returnCek' on values ('Delay', 'LamAbs', 'Constant', 'Builtin')
-- 3. returns 'EvaluationFailure' ('Error')
-- 4. looks up a variable in the environment and calls 'returnCek' ('Var')

-- See Note [Compilation peculiarities].
computeCek
    :: Ix fun
    => Context uni fun -> CekValEnv uni fun -> TermWithMem uni fun -> CekM cost uni fun s (Term Name uni fun ())
-- s ; ρ ▻ {L A}  ↦ s , {_ A} ; ρ ▻ L
computeCek ctx env (Var _ varName) = do
    spendBudget BVar astNodeCost
    val <- lookupVarName varName env
    returnCek ctx val
computeCek ctx _ (Constant ex val) = do
    spendBudget BConst astNodeCost
    returnCek ctx (VCon ex val)
computeCek ctx env (LamAbs ex name body) = do
    spendBudget BLamAbs astNodeCost
    returnCek ctx (VLamAbs ex name body env)
computeCek ctx env (Delay ex body) = do
    spendBudget BDelay astNodeCost
    returnCek ctx (VDelay ex body env)
-- s ; ρ ▻ lam x L  ↦  s ◅ lam x (L , ρ)
computeCek ctx env (Force _ body) = do
    spendBudget BForce astNodeCost
    computeCek (FrameForce : ctx) env body
-- s ; ρ ▻ [L M]  ↦  s , [_ (M,ρ)]  ; ρ ▻ L
computeCek ctx env (Apply _ fun arg) = do
    spendBudget BApply astNodeCost
    computeCek (FrameApplyArg env arg : ctx) env fun
-- s ; ρ ▻ abs α L  ↦  s ◅ abs α (L , ρ)
-- s ; ρ ▻ con c  ↦  s ◅ con c
-- s ; ρ ▻ builtin bn  ↦  s ◅ builtin bn arity arity [] [] ρ
computeCek ctx _ (Builtin ex bn) = do
    spendBudget BBuiltin astNodeCost
    BuiltinRuntime _ arity _ _ <- asksM $ lookupBuiltin bn . cekEnvRuntime
    returnCek ctx (VBuiltin ex bn arity arity 0 [])
-- s ; ρ ▻ error A  ↦  <> A
computeCek _ _ (Error _) = do
    spendBudget BError astNodeCost
    throwing_ _EvaluationFailure
-- s ; ρ ▻ x  ↦  s ◅ ρ[ x ]
-- | Call 'dischargeCekValue' over the received 'CekVal' and feed the resulting 'Term' to
-- 'throwingWithCause' as the cause of the failure.
throwingDischarged
    :: (MonadError (ErrorWithCause e (Term Name uni fun ())) m)
    => AReview e t -> t -> CekValue uni fun -> m x
throwingDischarged l t = throwingWithCause l t . Just . void . dischargeCekValue

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
returnCek
    :: Ix fun
    => Context uni fun -> CekValue uni fun -> CekM cost uni fun s (Term Name uni fun ())
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
    :: Ix fun
    => Context uni fun -> CekValue uni fun -> CekM cost uni fun s (Term Name uni fun ())
forceEvaluate ctx (VDelay _ body env) = computeCek ctx env body
forceEvaluate ctx val@(VBuiltin ex bn arity0 arity forces args) =
    case arity of
      []             ->
          throwingDischarged _MachineError EmptyBuiltinArityMachineError val
      TermArg:_      ->
      {- This should be impossible if we don't have zero-arity builtins:
         we will have found this case in an earlier call to forceEvaluate
         or applyEvaluate and called applyBuiltin. -}
          throwingDischarged _MachineError BuiltinTermArgumentExpectedMachineError val'
                        where val' = VBuiltin ex bn arity0 arity (forces + 1) args -- reconstruct the bad application
      TypeArg:arity' ->
          case arity' of
            [] -> applyBuiltin ctx bn args  -- Final argument is a type argument
            _  -> returnCek ctx $ VBuiltin ex bn arity0 arity' (forces + 1) args -- More arguments expected
forceEvaluate _ val =
        throwingDischarged _MachineError NonPolymorphicInstantiationMachineError val

-- | Apply a function to an argument and proceed.
-- If the function is a lambda 'lam x ty body' then extend the environment with a binding of @v@
-- to x@ and call 'computeCek' on the body.
-- If the function is a builtin application then check that it's expecting a term argument, and if
-- it's the final argument then apply the builtin to its arguments, return the result, or extend
-- the value with the new argument and call 'returnCek'. If v is anything else, fail.
applyEvaluate
    :: Ix fun
    => Context uni fun
    -> CekValue uni fun   -- lhs of application
    -> CekValue uni fun   -- rhs of application
    -> CekM cost uni fun s (Term Name uni fun ())
applyEvaluate ctx (VLamAbs _ name body env) arg =
    computeCek ctx (extendEnv name arg env) body
applyEvaluate ctx val@(VBuiltin ex bn arity0 arity forces args) arg = do
    case arity of
      []        -> throwingDischarged _MachineError EmptyBuiltinArityMachineError val
                -- Should be impossible: see forceEvaluate.
      TypeArg:_ -> throwingDischarged _MachineError UnexpectedBuiltinTermArgumentMachineError val'
                   where val' = VBuiltin ex bn arity0 arity forces (args++[arg]) -- reconstruct the bad application
      TermArg:arity' -> do
          let args' = args ++ [arg]
          case arity' of
            [] -> applyBuiltin ctx bn args' -- 'arg' was the final argument
            _  -> returnCek ctx $ VBuiltin ex bn arity0 arity' forces args'  -- More arguments expected
applyEvaluate _ val _ = throwingDischarged _MachineError NonFunctionalApplicationMachineError val

-- | Apply a builtin to a list of CekValue arguments
applyBuiltin
    :: Ix fun
    => Context uni fun
    -> fun
    -> [CekValue uni fun]
    -> CekM cost uni fun s (Term Name uni fun ())
applyBuiltin ctx bn args = do
  -- Turn the cause of a possible failure, being a 'CekValue', into a 'Term'.
  -- See Note [Being generic over @term@ in 'CekM'].
  let dischargeError = hoist $ withExceptT $ mapCauseInMachineException $ void . dischargeCekValue
  BuiltinRuntime sch _ f exF <- asksM $ lookupBuiltin bn . cekEnvRuntime
  result <- dischargeError $ applyTypeSchemed bn sch f exF args
  returnCek ctx result

-- See Note [Compilation peculiarities].
-- | Evaluate a term using the CEK machine and keep track of costing, logging is optional.
runCek
    :: ( Closed uni, uni `Everywhere` ExMemoryUsage
       , Ix fun, ExMemoryUsage fun
       )
    => BuiltinsRuntime fun (CekValue uni fun)
    -> ExBudgetMode cost uni fun
    -> Bool
    -> Term Name uni fun ()
    -> (Either (CekEvaluationException uni fun) (Term Name uni fun ()), cost, [String])
runCek runtime mode emitting term =
    runCekM runtime mode emitting $ do
        spendBudget BAST (ExBudget 0 (termAnn memTerm))
        computeCek [] mempty memTerm
  where
    memTerm = withMemory term
