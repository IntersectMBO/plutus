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
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE UndecidableInstances  #-}

module Language.PlutusCore.Evaluation.Machine.Cek
    ( CekValue(..)
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

{- [Note: Arities in VBuiltin] The VBuiltin value below contains two copies of the
   arity (list of TypeArg/TermArg pairs) for the relevant builtin.  The second
   of these is consumed as the builtin is instantiated and applied to arguments,
   to check that type and term arguments are interleaved correctly.  The first
   copy of the arity is left unaltered and only used by dischargeCekValue if we
   have to convert the frame back into a term (see mkBuiltinApplication).  An
   alternative would be to look up the full arity in mkBuiltinApplication, but
   that would require a lot of things to be monadic (including the PrettyBy
   instance for CekValue, which is a problem.)
-}

-- 'Values' for the modified CEK machine.
data CekValue uni =
    -- TODO: we probably want to store a @Some (ValueOf uni)@ here, but then we have trouble in
    -- 'readKnownCek'. I'll reconsider the way we deal with annotations once again.
    VCon (TermWithMem uni)
  | VTyAbs ExMemory TyName KindWithMem (TermWithMem uni) (CekValEnv uni)
  | VLamAbs ExMemory Name (TypeWithMem uni) (TermWithMem uni) (CekValEnv uni)
  | VIWrap ExMemory (TypeWithMem uni) (TypeWithMem uni) (CekValue uni)
  | VBuiltin            -- A partial builtin application, accumulating arguments for eventual full application.
      ExMemory
      BuiltinName
      Arity             -- Sorts of arguments to be provided (both types and terms): *don't change this*.
      Arity             -- A copy of the arity used for checking applications/instantiatons: see [Note: Arities in VBuiltin]
      [TypeWithMem uni] -- The types the builtin is to be instantiated at.
                        -- We need these to construct a term if the machine is returning a stuck partial application.
      [CekValue uni]    -- Arguments we've computed so far.
      (CekValEnv uni)   -- Initial environment, used for evaluating every argument
    deriving (Show, Eq) -- Eq is just for tests.

type CekValEnv uni = UniqueMap TermUnique (CekValue uni)

-- | The environment the CEK machine runs in.
data CekEnv uni = CekEnv
    { cekEnvMeans              :: DynamicBuiltinNameMeanings (CekValue uni)
    , _cekEnvBudgetMode        :: ExBudgetMode
    , _cekEnvBuiltinCostParams :: CostModel
    }

data CekUserError
    = CekOutOfExError ExRestrictingBudget ExBudget
    | CekEvaluationFailure -- ^ Error has been called.
    deriving (Show, Eq)

-- | The CEK machine-specific 'EvaluationException'.
type CekEvaluationException uni =
    EvaluationException UnknownDynamicBuiltinNameError CekUserError (CekValue uni)

instance Pretty CekUserError where
    pretty (CekOutOfExError (ExRestrictingBudget res) b) =
        group $ "The limit" <+> prettyClassicDef res <+> "was reached by the execution environment. Final state:" <+> prettyClassicDef b
    pretty CekEvaluationFailure = "The provided Plutus code called 'error'."

-- | The monad the CEK machine runs in. State is inside the ExceptT, so we can
-- get it back in case of error.
type CekM uni = ReaderT (CekEnv uni) (ExceptT (CekEvaluationException uni) (State ExBudgetState))

{- | [Note: errors and CekValues] Most errors take an optional argument that can
   be used to report the term causing the error. Our builtin applications take
   CekValues as arguments, and this constrains the `term` type in the constant
   application machinery to be equal to `CekValue`.  This (I think) means that
   our errors can only involve CekValues and not Terms, so in some cases we
   can't provide any context when an error occurs (eg, if we try to look up a
   free variable in an environment: there's no CekValue for Var, so we can't
   report which variable caused the error.
-}

makeLenses ''CekEnv

arityOf :: BuiltinName -> CekM uni Arity
arityOf (StaticBuiltinName name) =
    pure $ builtinNameArities ! name
arityOf (DynBuiltinName name) = do
    DynamicBuiltinNameMeaning sch _ _ <- lookupDynamicBuiltinName name
    pure $ getArity sch
-- TODO: have a table of dynamic arities so that we don't have to do this computation every time.

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
   division by zero; the term is discarded in that case anyway (see [Note:
   Ignoring context in UserEvaluationError] in Exception.hs)
-}
mkBuiltinApplication :: ExMemory -> BuiltinName -> Arity -> [TypeWithMem uni] -> [TermWithMem uni] -> TermWithMem uni
mkBuiltinApplication ex bn arity0 tys0 args0 =
  go arity0 tys0 args0 (Builtin ex bn)
    where go arity tys args term =
              case (arity, args, tys) of
                ([], [], [])                        -> term   -- We've got to the end and successfully constructed the entire application
                (TermArg:arity', arg:args', _)      -> go arity' tys args' (Apply ex term arg)  -- got an expected term argument
                (TermArg:_,      [],       ty:_)    -> TyInst ex term ty                        -- term expected, type found
                (TypeArg:arity', _,        ty:tys') -> go arity' tys' args (TyInst ex term ty)  -- got an expected type argument
                (TypeArg:_,      arg:_,    [])      -> Apply ex term arg                        -- type expected, term found
                _                                   -> term                                     -- something else, including partial application

-- see Note [Scoping].
-- | Instantiate all the free variables of a term by looking them up in an environment.
-- Mutually recursive with dischargeCekVal.
dischargeCekValEnv :: CekValEnv uni -> TermWithMem uni -> TermWithMem uni
dischargeCekValEnv valEnv =
    -- We recursively discharge the environments of Cek values, but we will gradually end up doing
    -- this to terms which have no free variables remaining, at which point we won't call this
    -- substitution function any more and so we will terminate.
    termSubstFreeNames $ \name -> do
        val <- lookupName name valEnv
        Just $ dischargeCekValue val

-- Convert a CekValue into a term by replacing all bound variables with the terms
-- they're bound to (which themselves have to be obtain by recursively discharging values).
dischargeCekValue :: CekValue uni -> TermWithMem uni
dischargeCekValue = \case
    VCon t                                 -> t
    VTyAbs   ex tn k body env              -> TyAbs ex tn k (dischargeCekValEnv env body)
    VLamAbs  ex name ty body env           -> LamAbs ex name ty (dischargeCekValEnv env body)
    VIWrap   ex ty1 ty2 val                -> IWrap ex ty1 ty2 $ dischargeCekValue val
    VBuiltin ex bn arity0 _ tyargs args  _ -> mkBuiltinApplication ex bn arity0 tyargs (fmap dischargeCekValue args)
    {- We only discharge a value when (a) it's being returned by the machine,
       or (b) it's needed for an error message.  When we're discharging VBuiltin
       we use arity0 to get the type and term arguments into the right sequence. -}

instance (Closed uni, GShow uni, uni `Everywhere` PrettyConst) => PrettyBy PrettyConfigPlc (CekValue uni) where
    prettyBy cfg = prettyBy cfg . dischargeCekValue

type instance UniOf (CekValue uni) = uni

instance (Closed uni, uni `Everywhere` ExMemoryUsage) => FromConstant (CekValue uni) where
    fromConstant = VCon . fromConstant

instance AsConstant (CekValue uni) where
    asConstant (VCon term) = asConstant term
    asConstant _           = Nothing

instance ToExMemory (CekValue uni) where
    toExMemory = \case
        VCon t -> termAnn t
        VTyAbs ex _ _ _ _ -> ex
        VLamAbs ex _ _ _ _ -> ex
        VIWrap ex _ _ _ -> ex
        VBuiltin ex _ _ _ _ _ _ -> ex

instance SpendBudget (CekM uni) (CekValue uni) where
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
    = FrameApplyFun (CekValue uni)                               -- ^ @[V _]@
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

-- | Extend an environment with a variable name, the value the variable stands for
-- and the environment the value is defined in.
extendEnv :: Name -> CekValue uni -> CekValEnv uni -> CekValEnv uni
extendEnv argName arg  =
    insertByName argName arg

-- | Look up a variable name in the environment.
lookupVarName :: Name -> CekValEnv uni -> CekM uni (CekValue uni)
lookupVarName varName varEnv = do
    case lookupName varName varEnv of
        Nothing  -> throwingWithCause _MachineError OpenTermEvaluatedMachineError $ Nothing
                    -- No value available for error
        Just val -> pure val

-- | Look up a 'DynamicBuiltinName' in the environment.
lookupDynamicBuiltinName
    :: DynamicBuiltinName -> CekM uni (DynamicBuiltinNameMeaning (CekValue uni))
lookupDynamicBuiltinName dynName = do
    DynamicBuiltinNameMeanings means <- asks cekEnvMeans
    case Map.lookup dynName means of
        Nothing   -> throwingWithCause _MachineError err Nothing where
            err  = OtherMachineError $ UnknownDynamicBuiltinNameErrorE dynName
        Just mean -> pure mean

-- | The computing part of the CEK machine.
-- Either
-- 1. adds a frame to the context and calls 'computeCek' ('TyInst', 'Apply', 'IWrap', 'Unwrap')
-- 2. calls 'returnCek' on values ('TyAbs', 'LamAbs', 'Constant', 'Builtin')
-- 3. returns 'EvaluationFailure' ('Error')
-- 4. looks up a variable in the environment and calls 'returnCek' ('Var')

computeCek
    :: (GShow uni, GEq uni, DefaultUni <: uni, Closed uni, uni `Everywhere` ExMemoryUsage)
    => Context uni -> CekValEnv uni -> TermWithMem uni -> CekM uni (Plain Term uni)
-- s ; ρ ▻ {L A}  ↦ s , {_ A} ; ρ ▻ L
computeCek ctx env (TyInst _ body ty) = do
    spendBudget BTyInst (ExBudget 1 1) -- TODO
    computeCek (FrameTyInstArg ty : ctx) env body
-- s ; ρ ▻ [L M]  ↦  s , [_ (M,ρ)]  ; ρ ▻ L
computeCek ctx env (Apply _ fun arg) = do
    spendBudget BApply (ExBudget 1 1) -- TODO
    computeCek (FrameApplyArg env arg : ctx) env fun
-- s ; ρ ▻ wrap A B L  ↦  s , wrap A B _ ; ρ ▻ L
computeCek ctx env (IWrap ann pat arg term) = do
    spendBudget BIWrap (ExBudget 1 1) -- TODO
    computeCek (FrameIWrap ann pat arg : ctx) env term
-- s ; ρ ▻ unwrap L  ↦  s , unwrap _ ; ρ ▻ L
computeCek ctx env (Unwrap _ term) = do
    spendBudget BUnwrap (ExBudget 1 1) -- TODO
    computeCek (FrameUnwrap : ctx) env term
-- s ; ρ ▻ abs α L  ↦  s ◅ abs α (L , ρ)
computeCek ctx env (TyAbs ex tn k body) =
    -- TODO: budget?
    returnCek ctx (VTyAbs ex tn k body env)
-- s ; ρ ▻ lam x L  ↦  s ◅ lam x (L , ρ)
computeCek ctx env (LamAbs ex name ty body) =
    -- TODO: budget?
    returnCek ctx (VLamAbs ex name ty body env)
-- s ; ρ ▻ con c  ↦  s ◅ con c
computeCek ctx _ c@Constant{} =
    -- TODO: budget?
    returnCek ctx (VCon c)
-- s ; ρ ▻ builtin bn  ↦  s ◅ builtin bn arity arity [] [] ρ
computeCek ctx env (Builtin ex bn) = do
    -- TODO: budget?
  arity <- arityOf bn
  returnCek ctx (VBuiltin ex bn arity arity [] [] env)
-- s ; ρ ▻ error A  ↦  <> A
computeCek _ _  Error{} =
    throwingWithCause _EvaluationError (UserEvaluationError CekEvaluationFailure) Nothing -- No value available for error
-- s ; ρ ▻ x  ↦  s ◅ ρ[ x ]
computeCek ctx env (Var _ varName) = do
    spendBudget BVar (ExBudget 1 1) -- TODO
    val <- lookupVarName varName env
    returnCek ctx val

-- | The returning phase of the CEK machine.
-- Returns 'EvaluationSuccess' in case the context is empty, otherwise pops up one frame
-- from the context and uses it to decide how to proceed with the current value v.
--  'FrameTyInstArg': call instantiateEvaluate.  If v is a lambda then discard the type
--     and compute the body of v; if v is a builtin application then check that
--     it's expecting a type argument, either apply the builtin to its arguments or
--     and return the result, or extend the value with the type and call returnCek;
--     if v is anything else, fail.
--  'FrameApplyArg': call applyEvaluate. If v is a lambda then discard the type
--     and compute the body of v; if v is a builtin application then check that
--     it's expecting a type argument, either apply the builtin to its arguments
--     and return the result, or extend the value with the type and call returnCek;
--     if v is anything else, fail.
--  'FrameApplyFun': call applyEvaluate to attempt to apply the function
--     stored in the frame to an argument.  If the function is a lambda 'lam x ty body'
--     then extend the environment with a binding of v to x and call computeCek on the body.
--     If the is a builtin application then check that it's expecting a term argument,
--     and if it's the final argument then apply the builtin to its arguments
--     return the result, or extend the value with the new argument and call
--     returnCek.  If v is anything else, fail.
--  'FrameIWrap':  wrap v and call returnCek on the wrapped value.
--  'FrameUnwrap': if v is a wrapped value w then returnCek w, else fail.
returnCek
    :: (GShow uni, GEq uni, DefaultUni <: uni, Closed uni, uni `Everywhere` ExMemoryUsage)
    => Context uni -> CekValue uni -> CekM uni (Plain Term uni)
--- Instantiate all the free variable of the resulting term in case there are any.
-- . ◅ V           ↦  [] V
returnCek [] val = pure $ void $ dischargeCekValue val
-- s , {_ A} ◅ abs α M  ↦  s ; ρ ▻ M [ α / A ]*
returnCek (FrameTyInstArg ty : ctx) fun = instantiateEvaluate ctx ty fun
-- s , [_ (M,ρ)] ◅ V  ↦  s , [V _] ; ρ ▻ M
returnCek (FrameApplyArg argVarEnv arg : ctx) fun = do
    computeCek (FrameApplyFun fun : ctx) argVarEnv arg
-- s , [(lam x (M,ρ)) _] ◅ V  ↦  s ; ρ [ x  ↦  V ] ▻ M
-- FIXME: add rule for VBuiltin once it's in the specification.
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

{- [Note: accumulating arguments].  The VBuiltin value contains lists of type and term
 arguments which grow as new arguments are encountered.  In the code below We just add
 new entries by appending to the end of the list: l -> l++[x].  This doesn't look
 terrbily good, but we don't expect the lists to ever contain more than three or four
 elements, so the cost is unlikely to be high.  We could accumulate lists in the normal
 way and reverse them when required, but this is error-prone and reversal adds an extra
 cost anyway.  We could also use something like Data.Sequence, but again we incur an
 extra cost because we have to convert to a normal list when passing the arguments to
 the constant application machinery.  If we really care we might want to convert the CAM
 to use sequences instead of lists.
-}

-- | Instantiate a term with a type and proceed.
-- In case of 'VTyAbs' just ignore the type; for 'VBuiltin', extend
-- the type arguments with the type, decrement the argument count,
-- and proceed; otherwise, it's an error.
instantiateEvaluate
    :: (GShow uni, GEq uni, DefaultUni <: uni, Closed uni, uni `Everywhere` ExMemoryUsage)
    => Context uni -> Type TyName uni ExMemory -> CekValue uni -> CekM uni (Plain Term uni)
instantiateEvaluate ctx _ (VTyAbs _ _ _ body env) = computeCek ctx env body
instantiateEvaluate ctx ty val@(VBuiltin ex bn arity0 arity tyargs args argEnv) =
    case arity of
      []             -> throwingWithCause _MachineError EmptyBuiltinArityMachineError $ Just val
                     {- This should be impossible if we don't have zero-arity builtins:
                        we will have found this case in an earlier call to instantiateEvaluate
                        or applyEvaluate and called applyBuiltinName. -}
      TermArg:_      -> throwingWithCause _MachineError UnexpectedBuiltinInstantiationMachineError $ Just val'
                        where val' = VBuiltin ex bn arity0 arity (tyargs++[ty]) args argEnv -- reconstruct the bad application
      TypeArg:arity' ->
          case arity' of
            [] -> applyBuiltinName ctx bn args  -- Final argument is a type argument
            _  -> returnCek ctx $ VBuiltin ex bn arity0 arity' (tyargs++[ty]) args argEnv -- More arguments expected
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
    -> CekValue uni   -- lsh of application
    -> CekValue uni   -- rhs of application
    -> CekM uni (Plain Term uni)
applyEvaluate ctx (VLamAbs _ name _ty body env) arg =
    computeCek ctx (extendEnv name arg env) body
applyEvaluate ctx val@(VBuiltin ex bn arity0 arity tyargs args argEnv) arg =do
    case arity of
      []        -> throwingWithCause _MachineError EmptyBuiltinArityMachineError $ Just val
                -- Should be impossible: see instantiateEvaluate.
      TypeArg:_ -> throwingWithCause _MachineError UnexpectedBuiltinTermArgumentMachineError $ Just val'
                   where val' = VBuiltin ex bn arity0 arity tyargs (args++[arg]) argEnv -- reconstruct the bad application
      TermArg:arity' -> do
          let args' = args ++ [arg]
          case arity' of
            [] -> applyBuiltinName ctx bn args' -- 'arg' was the final argument
            _  -> returnCek ctx $ VBuiltin ex bn arity0 arity' tyargs args' argEnv  -- More arguments expected
applyEvaluate _ val _ = throwingWithCause _MachineError NonFunctionalApplicationMachineError $ Just val

-- | Apply a builtin to a list of CekValue arguments
applyBuiltinName
    :: (GShow uni, GEq uni, DefaultUni <: uni, Closed uni, uni `Everywhere` ExMemoryUsage)
    => Context uni
    -> BuiltinName
    -> [CekValue uni]
    -> CekM uni (Plain Term uni)
applyBuiltinName ctx bn args = do
  result <- case bn of
           n@(DynBuiltinName name) -> do
               DynamicBuiltinNameMeaning sch x exX <- lookupDynamicBuiltinName name
               applyTypeSchemed n sch x exX args
           StaticBuiltinName name ->
               applyStaticBuiltinName name args
  case result of
    EvaluationSuccess t -> returnCek ctx t
    EvaluationFailure ->
        throwingWithCause _EvaluationError (UserEvaluationError CekEvaluationFailure) $ Nothing
        {- NB: we're not reporting any context here.  When UserEvaluationError is
           invloved, Exception.extractEvaluationResult just throws the cause
           away (see [Note: Ignoring context in UserEvaluationError]), so it
           doesn't matter if we don't have any context. We could provide
           applyBuiltinName with sufficient information to reconstruct the
           application, but that would add a cost without adding any benefit. -}

-- | Evaluate a term using the CEK machine and keep track of costing.
runCek
    :: (GShow uni, GEq uni, DefaultUni <: uni, Closed uni, uni `Everywhere` ExMemoryUsage)
    => DynamicBuiltinNameMeanings (CekValue uni)
    -> ExBudgetMode
    -> CostModel
    -> Plain Term uni
    -> (Either (CekEvaluationException uni) (Plain Term uni), ExBudgetState)
runCek means mode params term =
    runCekM (CekEnv means mode params)
            (ExBudgetState mempty mempty)
        $ do
            spendBudget BAST (ExBudget 0 (termAnn memTerm))
            computeCek [] mempty memTerm
    where
        memTerm = withMemory term

-- | Evaluate a term using the CEK machine in the 'Counting' mode.
runCekCounting
    :: (GShow uni, GEq uni, DefaultUni <: uni, Closed uni, uni `Everywhere` ExMemoryUsage)
    => DynamicBuiltinNameMeanings (CekValue uni)
    -> CostModel
    -> Plain Term uni
    -> (Either (CekEvaluationException uni) (Plain Term uni), ExBudgetState)
runCekCounting means = runCek means Counting

-- | Evaluate a term using the CEK machine.
evaluateCek
    :: (GShow uni, GEq uni, DefaultUni <: uni, Closed uni, uni `Everywhere` ExMemoryUsage)
    => DynamicBuiltinNameMeanings (CekValue uni)
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
    => DynamicBuiltinNameMeanings (CekValue uni)
    -> CostModel
    -> Plain Term uni
    -> EvaluationResult (Plain Term uni)
unsafeEvaluateCek means params = either throw id . extractEvaluationResult . evaluateCek means params

-- | Unlift a value using the CEK machine.
readKnownCek
    :: ( GShow uni, GEq uni, DefaultUni <: uni, Closed uni, uni `Everywhere` ExMemoryUsage
       , KnownType (Plain Term uni) a
       )
    => DynamicBuiltinNameMeanings (CekValue uni)
    -> CostModel
    -> Plain Term uni
    -> Either (CekEvaluationException uni) a
-- Calling 'withMemory' just to unify the monads that 'readKnown' and the CEK machine run in.
readKnownCek means params = evaluateCek means params >=> first (fmap $ VCon . withMemory) . readKnown
