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
{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE UndecidableInstances  #-}

module Language.UntypedPlutusCore.Evaluation.Machine.Cek
    ( CekValue(..)
    , CekEvaluationException
    , EvaluationResult(..)
    , ErrorWithCause(..)
    , EvaluationError(..)
    , ExBudget(..)
    , ExBudgetCategory(..)
    , ExBudgetMode(..)
    , ExRestrictingBudget(..)
    , ExTally(..)
    , CekExBudgetState
    , CekExTally
    , exBudgetStateTally
    , extractEvaluationResult
    , runCek
    , runCekCounting
    , evaluateCek
    , unsafeEvaluateCek
    , readKnownCek
    , annotateMemory
    )
where

import           PlutusPrelude

import           Language.UntypedPlutusCore.Core
import           Language.UntypedPlutusCore.Subst

import           Language.PlutusCore.Constant
import           Language.PlutusCore.Evaluation.Machine.ExBudgeting
import           Language.PlutusCore.Evaluation.Machine.ExMemory
import           Language.PlutusCore.Evaluation.Machine.Exception
import           Language.PlutusCore.Evaluation.Result
import           Language.PlutusCore.Name
import           Language.PlutusCore.Pretty
import           Language.PlutusCore.Universe

import           Control.Lens                                       (AReview)
import           Control.Lens.Operators
import           Control.Lens.Setter
import           Control.Monad.Except
import           Control.Monad.Morph
import           Control.Monad.Reader
import           Control.Monad.State.Strict
import           Data.Array
import           Data.HashMap.Monoidal
import           Data.Text.Prettyprint.Doc

import           Data.Functor.Foldable                              (Recursive (cata))
import qualified Data.Vector                                        as Vector
import           Language.PlutusCore.Core.Type                      (ToAnnotation (toAnnotation))

{- Note [Scoping]
   The CEK machine does not rely on the global uniqueness condition, so the renamer pass is not a
   prerequisite. The CEK machine correctly handles name shadowing.
-}

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
      (CekValEnv uni fun)   -- Initial environment, used for evaluating every argument
    deriving (Show, Eq) -- Eq is just for tests.

instance ToExMemory (CekValue uni fun) where
    toExMemory (VCon mem _)               = mem
    toExMemory (VDelay mem _ _)           = mem
    toExMemory (VLamAbs mem _ _ _)        = mem
    toExMemory (VBuiltin mem _ _ _ _ _ _) = mem

type CekValEnv uni fun = UniqueMap TermUnique (CekValue uni fun)

-- | The environment the CEK machine runs in.
data CekEnv uni fun = CekEnv
    { cekEnvRuntime    :: BuiltinsRuntime fun (CekValue uni fun)
    , cekEnvBudgetMode :: ExBudgetMode
    }

data CekUserError
    = CekOutOfExError ExRestrictingBudget ExBudget
    | CekEvaluationFailure -- ^ Error has been called or a builtin application has failed
    deriving (Show, Eq)

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
    EvaluationException CekUserError fun term

-- See Note [Being generic over @term@ in 'CekM'].
-- | A generalized version of 'CekM' carrying a @term@.
-- 'State' is inside the 'ExceptT', so we can get it back in case of error.
type CekCarryingM term uni fun =
    ReaderT (CekEnv uni fun) (ExceptT (CekEvaluationExceptionCarrying term fun) (State (CekExBudgetState fun)))

-- | The CEK machine-specific 'EvaluationException'.
type CekEvaluationException uni fun = CekEvaluationExceptionCarrying (Term Name uni fun ()) fun

-- | The monad the CEK machine runs in.
type CekM uni fun = CekCarryingM (Term Name uni fun ()) uni fun

data ExBudgetCategory fun
    = BForce
    | BApply
    | BVar
    | BDelay
    | BLamAbs
    | BBuiltin fun
    | BAST
    deriving stock (Show, Eq, Generic)
    deriving anyclass (NFData, Hashable)
instance Show fun => PrettyBy config (ExBudgetCategory fun) where
    prettyBy _ = viaShow

type CekExBudgetState fun = ExBudgetState (ExBudgetCategory fun)
type CekExTally fun       = ExTally       (ExBudgetCategory fun)

instance AsEvaluationFailure CekUserError where
    _EvaluationFailure = _EvaluationFailureVia CekEvaluationFailure

instance Pretty CekUserError where
    pretty (CekOutOfExError (ExRestrictingBudget res) b) =
        group $ "The limit" <+> prettyClassicDef res <+> "was reached by the execution environment. Final state:" <+> prettyClassicDef b
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
dischargeCekValEnv
    :: (Closed uni, uni `Everywhere` ExMemoryUsage)
    => CekValEnv uni fun -> TermWithMem uni fun -> TermWithMem uni fun
dischargeCekValEnv valEnv =
    -- We recursively discharge the environments of Cek values, but we will gradually end up doing
    -- this to terms which have no free variables remaining, at which point we won't call this
    -- substitution function any more and so we will terminate.
    termSubstFreeNames $ \name -> do
        val <- lookupName name valEnv
        Just $ dischargeCekValue val

-- Convert a CekValue into a term by replacing all bound variables with the terms
-- they're bound to (which themselves have to be obtain by recursively discharging values).
dischargeCekValue
    :: (Closed uni, uni `Everywhere` ExMemoryUsage)
    => CekValue uni fun -> TermWithMem uni fun
dischargeCekValue = \case
    VCon     ex val                        -> Constant ex val
    VDelay   ex body env                   -> Delay ex (dischargeCekValEnv env body)
    VLamAbs  ex name body env              -> LamAbs ex name (dischargeCekValEnv env body)
    VBuiltin ex bn arity0 _ forces args  _ -> mkBuiltinApplication ex bn arity0 forces (fmap dischargeCekValue args)
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

instance ExBudgetBuiltin fun (ExBudgetCategory fun) where
    exBudgetBuiltin = BBuiltin

-- We only need the @Eq fun@ constraint here and not anywhere else, because in other places we have
-- @Ix fun@ which implies @Ord fun@ which implies @Eq fun@.
instance (Eq fun, Hashable fun, ToExMemory term) =>
            SpendBudget (CekCarryingM term uni fun) fun (ExBudgetCategory fun) term where
    spendBudget key budget = do
        modifying exBudgetStateTally
                (<> ExTally (singleton key (Vector.singleton budget)))
        newBudget <- exBudgetStateBudget <%= (<> budget)
        mode <- asks cekEnvBudgetMode
        case mode of
            Counting -> pure ()
            Restricting resb ->
                when (exceedsBudget resb newBudget) $
                    throwingWithCause _EvaluationError
                        (UserEvaluationError $ CekOutOfExError resb newBudget)
                        Nothing  -- No value available for error

data Frame uni fun
    = FrameApplyFun (CekValue uni fun)                         -- ^ @[V _]@
    | FrameApplyArg (CekValEnv uni fun) (TermWithMem uni fun)  -- ^ @[_ N]@
    | FrameForce                                               -- ^ @(force _)@
    deriving (Show)

type Context uni fun = [Frame uni fun]

runCekM
    :: forall a uni fun
     . CekEnv uni fun
    -> CekExBudgetState fun
    -> CekM uni fun a
    -> (Either (CekEvaluationException uni fun) a, CekExBudgetState fun)
runCekM env s a = runState (runExceptT $ runReaderT a env) s

-- | Extend an environment with a variable name, the value the variable stands for
-- and the environment the value is defined in.
extendEnv :: Name -> CekValue uni fun -> CekValEnv uni fun -> CekValEnv uni fun
extendEnv = insertByName

-- | Look up a variable name in the environment.
lookupVarName :: Name -> CekValEnv uni fun -> CekM uni fun (CekValue uni fun)
lookupVarName varName varEnv = do
    case lookupName varName varEnv of
        Nothing  -> throwingWithCause _MachineError OpenTermEvaluatedMachineError $ Just var where
            var = Var () varName
        Just val -> pure val

-- | The computing part of the CEK machine.
-- Either
-- 1. adds a frame to the context and calls 'computeCek' ('Force', 'Apply')
-- 2. calls 'returnCek' on values ('Delay', 'LamAbs', 'Constant', 'Builtin')
-- 3. returns 'EvaluationFailure' ('Error')
-- 4. looks up a variable in the environment and calls 'returnCek' ('Var')

computeCek
    :: ( GShow uni, GEq uni, Closed uni, uni `Everywhere` ExMemoryUsage
       , Hashable fun, Ix fun
       )
    => Context uni fun -> CekValEnv uni fun -> TermWithMem uni fun -> CekM uni fun (Term Name uni fun ())
-- s ; ρ ▻ {L A}  ↦ s , {_ A} ; ρ ▻ L
computeCek ctx env (Force _ body) = do
    spendBudget BForce (ExBudget 1 1) -- TODO
    computeCek (FrameForce : ctx) env body
-- s ; ρ ▻ [L M]  ↦  s , [_ (M,ρ)]  ; ρ ▻ L
computeCek ctx env (Apply _ fun arg) = do
    spendBudget BApply (ExBudget 1 1) -- TODO
    computeCek (FrameApplyArg env arg : ctx) env fun
-- s ; ρ ▻ abs α L  ↦  s ◅ abs α (L , ρ)
computeCek ctx env (Delay ex body) = do
    spendBudget BDelay (ExBudget 1 1) -- TODO
    returnCek ctx (VDelay ex body env)
-- s ; ρ ▻ lam x L  ↦  s ◅ lam x (L , ρ)
computeCek ctx env (LamAbs ex name body) = do
    spendBudget BLamAbs (ExBudget 1 1) -- TODO
    returnCek ctx (VLamAbs ex name body env)
-- s ; ρ ▻ con c  ↦  s ◅ con c
computeCek ctx _ (Constant ex val) =
    returnCek ctx (VCon ex val)
-- s ; ρ ▻ builtin bn  ↦  s ◅ builtin bn arity arity [] [] ρ
computeCek ctx env (Builtin ex bn) = do
  BuiltinRuntime _ arity _ _ <- asksM $ lookupBuiltin bn . cekEnvRuntime
  returnCek ctx (VBuiltin ex bn arity arity 0 [] env)
-- s ; ρ ▻ error A  ↦  <> A
computeCek _ _ (Error _) =
    throwingWithCause _EvaluationError (UserEvaluationError CekEvaluationFailure) . Just $ Error ()
-- s ; ρ ▻ x  ↦  s ◅ ρ[ x ]
computeCek ctx env (Var _ varName) = do
    spendBudget BVar (ExBudget 1 1) -- TODO
    val <- lookupVarName varName env
    returnCek ctx val

-- | Call 'dischargeCekValue' over the received 'CekVal' and feed the resulting 'Term' to
-- 'throwingWithCause' as the cause of the failure.
throwingDischarged
    :: ( MonadError (ErrorWithCause e (Term Name uni fun ())) m
       , Closed uni, uni `Everywhere` ExMemoryUsage
       )
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
    :: ( GShow uni, GEq uni, Closed uni, uni `Everywhere` ExMemoryUsage
       , Hashable fun, Ix fun
       )
    => Context uni fun -> CekValue uni fun -> CekM uni fun (Term Name uni fun ())
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
    :: ( GShow uni, GEq uni, Closed uni, uni `Everywhere` ExMemoryUsage
       , Hashable fun, Ix fun
       )
    => Context uni fun -> CekValue uni fun -> CekM uni fun (Term Name uni fun ())
forceEvaluate ctx (VDelay _ body env) = computeCek ctx env body
forceEvaluate ctx val@(VBuiltin ex bn arity0 arity forces args argEnv) =
    case arity of
      []             ->
          throwingDischarged _MachineError EmptyBuiltinArityMachineError val
      TermArg:_      ->
      {- This should be impossible if we don't have zero-arity builtins:
         we will have found this case in an earlier call to forceEvaluate
         or applyEvaluate and called applyBuiltin. -}
          throwingDischarged _MachineError BuiltinTermArgumentExpectedMachineError val'
                        where val' = VBuiltin ex bn arity0 arity (forces + 1) args argEnv -- reconstruct the bad application
      TypeArg:arity' ->
          case arity' of
            [] -> applyBuiltin ctx bn args  -- Final argument is a type argument
            _  -> returnCek ctx $ VBuiltin ex bn arity0 arity' (forces + 1) args argEnv -- More arguments expected
forceEvaluate _ val =
        throwingDischarged _MachineError NonPolymorphicInstantiationMachineError val

-- | Apply a function to an argument and proceed.
-- If the function is a lambda 'lam x ty body' then extend the environment with a binding of @v@
-- to x@ and call 'computeCek' on the body.
-- If the function is a builtin application then check that it's expecting a term argument, and if
-- it's the final argument then apply the builtin to its arguments, return the result, or extend
-- the value with the new argument and call 'returnCek'. If v is anything else, fail.
applyEvaluate
    :: ( GShow uni, GEq uni, Closed uni, uni `Everywhere` ExMemoryUsage
       , Hashable fun, Ix fun
       )
    => Context uni fun
    -> CekValue uni fun   -- lhs of application
    -> CekValue uni fun   -- rhs of application
    -> CekM uni fun (Term Name uni fun ())
applyEvaluate ctx (VLamAbs _ name body env) arg =
    computeCek ctx (extendEnv name arg env) body
applyEvaluate ctx val@(VBuiltin ex bn arity0 arity forces args argEnv) arg = do
    case arity of
      []        -> throwingDischarged _MachineError EmptyBuiltinArityMachineError val
                -- Should be impossible: see forceEvaluate.
      TypeArg:_ -> throwingDischarged _MachineError UnexpectedBuiltinTermArgumentMachineError val'
                   where val' = VBuiltin ex bn arity0 arity forces (args++[arg]) argEnv -- reconstruct the bad application
      TermArg:arity' -> do
          let args' = args ++ [arg]
          case arity' of
            [] -> applyBuiltin ctx bn args' -- 'arg' was the final argument
            _  -> returnCek ctx $ VBuiltin ex bn arity0 arity' forces args' argEnv  -- More arguments expected
applyEvaluate _ val _ = throwingDischarged _MachineError NonFunctionalApplicationMachineError val

-- | Apply a builtin to a list of CekValue arguments
applyBuiltin
    :: ( GShow uni, GEq uni, Closed uni, uni `Everywhere` ExMemoryUsage
       , Hashable fun, Ix fun
       )
    => Context uni fun
    -> fun
    -> [CekValue uni fun]
    -> CekM uni fun (Term Name uni fun ())
applyBuiltin ctx bn args = do
  -- Turn the cause of a possible failure, being a 'CekValue', into a 'Term'.
  -- See Note [Being generic over @term@ in 'CekM'].
  let dischargeError = hoist $ withExceptT $ mapErrorWithCauseF $ void . dischargeCekValue
  BuiltinRuntime sch _ f exF <- asksM $ lookupBuiltin bn . cekEnvRuntime
  result <- dischargeError $ applyTypeSchemed bn sch f exF args
  returnCek ctx result

-- | Evaluate a term using the CEK machine and keep track of costing.
runCek
    :: ( GShow uni, GEq uni, Closed uni, uni `Everywhere` ExMemoryUsage
       , Hashable fun, Ix fun
       )
    => BuiltinsRuntime fun (CekValue uni fun)
    -> ExBudgetMode
    -> Term Name uni fun ()
    -> (Either (CekEvaluationException uni fun) (Term Name uni fun ()), CekExBudgetState fun)
runCek runtime mode term =
    runCekM (CekEnv runtime mode)
            (ExBudgetState mempty mempty)
        $ do
            spendBudget BAST (ExBudget 0 (toAnnotation memTerm))
            computeCek [] mempty memTerm
    where
        memTerm = annotateMemory term

-- | Evaluate a term using the CEK machine in the 'Counting' mode.
runCekCounting
    :: ( GShow uni, GEq uni, Closed uni, uni `Everywhere` ExMemoryUsage
       , Hashable fun, Ix fun
       )
    => BuiltinsRuntime fun (CekValue uni fun)
    -> Term Name uni fun ()
    -> (Either (CekEvaluationException uni fun) (Term Name uni fun ()), CekExBudgetState fun)
runCekCounting means = runCek means Counting

-- | Evaluate a term using the CEK machine.
evaluateCek
    :: ( GShow uni, GEq uni, Closed uni, uni `Everywhere` ExMemoryUsage
       , Hashable fun, Ix fun
       )
    => BuiltinsRuntime fun (CekValue uni fun)
    -> Term Name uni fun ()
    -> Either (CekEvaluationException uni fun) (Term Name uni fun ())
evaluateCek runtime = fst . runCekCounting runtime

-- | Evaluate a term using the CEK machine. May throw a 'CekMachineException'.
unsafeEvaluateCek
    :: ( GShow uni, GEq uni, Typeable uni
       , Closed uni, uni `EverywhereAll` '[ExMemoryUsage, PrettyConst]
       , Hashable fun, Ix fun, Pretty fun, Typeable fun
       )
    => BuiltinsRuntime fun (CekValue uni fun)
    -> Term Name uni fun ()
    -> EvaluationResult (Term Name uni fun ())
unsafeEvaluateCek runtime = either throw id . extractEvaluationResult . evaluateCek runtime

-- | Unlift a value using the CEK machine.
readKnownCek
    :: ( GShow uni, GEq uni, Closed uni, uni `Everywhere` ExMemoryUsage
       , KnownType (Term Name uni fun ()) a
       , Hashable fun, Ix fun
       )
    => BuiltinsRuntime fun (CekValue uni fun)
    -> Term Name uni fun ()
    -> Either (CekEvaluationException uni fun) a
readKnownCek runtime = evaluateCek runtime >=> readKnown

annotateMemory :: (Everywhere uni ExMemoryUsage, Closed uni) =>
    Term Name uni fun () -> Term Name uni fun ExMemory
annotateMemory = cata $ \case
    ConstantF () som      -> Constant (constructorMemoryUsage + memoryUsage som) som
    BuiltinF () fun       -> Builtin constructorMemoryUsage fun
    VarF () name          -> Var (constructorMemoryUsage + memoryUsage name) name
    LamAbsF () name term  -> LamAbs (constructorMemoryUsage + toAnnotation term + memoryUsage name) name term
    ApplyF () term1 term2 -> Apply (constructorMemoryUsage + toAnnotation term1 + toAnnotation term2) term1 term2
    DelayF () term        -> Delay (constructorMemoryUsage + toAnnotation term) term
    ForceF () term        -> Force (constructorMemoryUsage + toAnnotation term) term
    ErrorF ()             -> Error constructorMemoryUsage
    where
        constructorMemoryUsage = 1
