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

module Language.UntypedPlutusCore.Evaluation.Machine.Cek.Type
    ( EvaluationResult(..)
    , CekValue(..)
    , CekUserError(..)
    , CekEvaluationException
    , BudgetSpender(..)
    , CekM
    , ErrorWithCause(..)
    , EvaluationError(..)
    , ExBudgetCategory(..)
    , extractEvaluationResult
    , runCekM
    , computeCek
    )
where

import           ErrorCode
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
import           Control.Monad.Except
import           Control.Monad.Morph
import           Control.Monad.Reader
import           Control.Monad.ST
import           Control.Monad.State.Strict
import           Data.Array
import           Data.DList                                         (DList)
import qualified Data.DList                                         as DList
import           Data.STRef
import           Data.Text.Prettyprint.Doc

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
instance Show fun => PrettyBy config (ExBudgetCategory fun) where
    prettyBy _ = viaShow

instance ExBudgetBuiltin fun (ExBudgetCategory fun) where
    exBudgetBuiltin = BBuiltinApp

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
    deriving (Show, Eq) -- Eq is just for tests.

type CekValEnv uni fun = UniqueMap TermUnique (CekValue uni fun)

-- | The environment the CEK machine runs in.
data CekEnv st uni fun s = CekEnv
    { cekEnvRuntime       :: BuiltinsRuntime fun (CekValue uni fun)
    -- 'Nothing' means no logging. 'DList' is due to the fact that we need efficient append
    -- as we store logs as "latest go last".
    , cekEnvMayEmitRef    :: Maybe (STRef s (DList String))
    , cekEnvBudgetSpender :: BudgetSpender st uni fun
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
type CekCarryingM st term uni fun s =
    ReaderT (CekEnv st uni fun s)
        (ExceptT (CekEvaluationExceptionCarrying term fun)
            (StateT st
                (ST s)))

-- | The CEK machine-specific 'EvaluationException'.
type CekEvaluationException uni fun = CekEvaluationExceptionCarrying (Term Name uni fun ()) fun

-- | The monad the CEK machine runs in.
type CekM st uni fun s = CekCarryingM st (Term Name uni fun ()) uni fun s

instance AsEvaluationFailure CekUserError where
    _EvaluationFailure = _EvaluationFailureVia CekEvaluationFailure

instance Pretty CekUserError where
    pretty (CekOutOfExError (ExRestrictingBudget res)) =
        group $ "The budget was overspent. Final negative state:" <+> prettyClassicDef res
    pretty CekEvaluationFailure = "The provided Plutus code called 'error'."

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

instance MonadEmitter (CekCarryingM st term uni fun s) where
    emit str = do
        mayLogsRef <- asks cekEnvMayEmitRef
        case mayLogsRef of
            Nothing      -> pure ()
            Just logsRef -> lift . lift . lift $ modifySTRef logsRef (`DList.snoc` str)

data Frame uni fun
    = FrameApplyFun (CekValue uni fun)                         -- ^ @[V _]@
    | FrameApplyArg (CekValEnv uni fun) (TermWithMem uni fun)  -- ^ @[_ N]@
    | FrameForce                                               -- ^ @(force _)@
    deriving (Show)

type Context uni fun = [Frame uni fun]
