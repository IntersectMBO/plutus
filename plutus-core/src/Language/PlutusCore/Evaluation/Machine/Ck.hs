-- | The CK machine.

{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE LambdaCase                #-}
{-# LANGUAGE MultiParamTypeClasses     #-}
{-# LANGUAGE OverloadedStrings         #-}
{-# LANGUAGE TypeApplications          #-}
{-# LANGUAGE TypeFamilies              #-}
{-# LANGUAGE TypeOperators             #-}
{-# LANGUAGE UndecidableInstances      #-}

module Language.PlutusCore.Evaluation.Machine.Ck
    ( EvaluationResult (..)
    , CkEvaluationException
    , CkM
    , CkValue
    , evaluateCk
    , unsafeEvaluateCk
    ) where

import           PlutusPrelude

import           Language.PlutusCore.Constant
import           Language.PlutusCore.Core
import           Language.PlutusCore.Evaluation.Machine.ExBudgeting
import           Language.PlutusCore.Evaluation.Machine.Exception
import           Language.PlutusCore.Evaluation.Result
import           Language.PlutusCore.Name
import           Language.PlutusCore.Pretty                         (PrettyConfigPlc, PrettyConst)
import           Language.PlutusCore.Universe

import           Control.Monad.Reader
import           Data.Array

infix 4 |>, <|

{- See Note [Arities in VBuiltin] in Cek.hs -}
data CkValue uni fun =
    VCon (Term TyName Name uni fun ())  -- TODO: Really want a constant here.
  | VTyAbs TyName (Kind ()) (Term TyName Name uni fun ())
  | VLamAbs Name (Type TyName uni ()) (Term TyName Name uni fun ())
  | VIWrap (Type TyName uni ()) (Type TyName uni ()) (CkValue uni fun)
  | VBuiltin
      fun
      Arity                -- Sorts of arguments to be provided (both types and terms): *don't change this*.
      Arity                -- A copy of the arity used for checking applications/instantiatons: see Note [Arities in VBuiltin]
      [Type TyName uni ()] -- The types the builtin is to be instantiated at.
                           -- We need these to construct a term if the machine is returning a stuck partial application.
      [CkValue uni fun]        -- Arguments we've computed so far.
    deriving (Show, Eq)    -- Eq is just for tests.

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
   it has at that point.  Note that we don't call this function if a builtin
   fails for some reason like division by zero; the term is discarded in that
   case anyway (see Note [Ignoring context in UserEvaluationError] in
   Exception.hs)
-}
mkBuiltinApplication :: () -> fun -> Arity -> [Type TyName uni ()] -> [Term TyName Name uni fun ()] -> Term TyName Name uni fun ()
mkBuiltinApplication () bn arity0 tys0 args0 =
  go arity0 tys0 args0 (Builtin () bn)
    where go arity tys args term =
              case (arity, args, tys) of
                ([], [], [])                        -> term   -- We've got to the end and successfully constructed the entire application
                (TermArg:arity', arg:args', _)      -> go arity' tys args' (Apply () term arg)  -- got an expected term argument
                (TermArg:_,      [],       ty:_)    -> TyInst () term ty                        -- term expected, type found
                (TypeArg:arity', _,        ty:tys') -> go arity' tys' args (TyInst () term ty)  -- got an expected type argument
                (TypeArg:_,      arg:_,    [])      -> Apply () term arg                        -- type expected, term found
                _                                   -> term                                     -- something else, including partial application

ckValueToTerm :: () -> CkValue uni fun -> Term TyName Name uni fun ()
ckValueToTerm () = \case
    VCon t                           -> t
    VTyAbs  tn k body                -> TyAbs  () tn k body
    VLamAbs name ty body             -> LamAbs () name ty body
    VIWrap  ty1 ty2 val              -> IWrap  () ty1 ty2 $ ckValueToTerm () val
    VBuiltin bn arity0 _ tyargs args -> mkBuiltinApplication () bn arity0 tyargs (fmap (ckValueToTerm ()) args)
    {- When we're dealing with VBuiltin we use arity0 to get the type and
       term arguments into the right sequence. -}

instance (Closed uni, GShow uni, uni `Everywhere` PrettyConst, Pretty fun) =>
            PrettyBy PrettyConfigPlc (CkValue uni fun) where
    prettyBy cfg = prettyBy cfg . ckValueToTerm ()

data CkUserError =
    CkEvaluationFailure -- Error has been called or a builtin application has failed
    deriving (Show, Eq)

-- | The CK machine-specific 'EvaluationException'.
type CkEvaluationException uni fun =
    EvaluationException CkUserError fun (CkValue uni fun)

instance Pretty CkUserError where
    pretty CkEvaluationFailure = "The provided Plutus code called 'error'."

newtype CkEnv uni fun = CkEnv
    { ckEnvRuntime :: BuiltinsRuntime fun (CkValue uni fun)
    }

type CkM uni fun = ReaderT (CkEnv uni fun) (Either (CkEvaluationException uni fun))

{- | Note [Errors and CekValues]
Most errors take an optional argument that can be used to report the
term causing the error. Our builtin applications take CkValues as
arguments, and this constrains the `term` type in the constant
application machinery to be equal to `CkValue`.  This (I think) means
that our errors can only involve CkValues and not Terms, so in some
cases we can't provide any context when an error occurs (eg, if we try
to look up a free variable in an environment: there's no CkValue for
Var, so we can't report which variable caused the error.
-}

instance SpendBudget (CkM uni fun) fun () (CkValue uni fun) where
    spendBudget _key _budget = pure ()

type instance UniOf (CkValue uni fun) = uni

instance FromConstant (CkValue uni fun) where
    fromConstant = VCon . fromConstant

instance AsConstant (CkValue uni fun) where
    asConstant (VCon term) = asConstant term
    asConstant _           = Nothing

instance ToExMemory (CkValue uni fun) where
    toExMemory _ = 0


data Frame uni fun
    = FrameApplyFun (CkValue uni fun)                       -- ^ @[V _]@
    | FrameApplyArg (Term TyName Name uni fun ())           -- ^ @[_ N]@
    | FrameTyInstArg (Type TyName uni ())                   -- ^ @{_ A}@
    | FrameUnwrap                                           -- ^ @(unwrap _)@
    | FrameIWrap (Type TyName uni ()) (Type TyName uni ())  -- ^ @(iwrap A B _)@

type Context uni fun = [Frame uni fun]

-- | Substitute a 'Term' for a variable in a 'Term' that can contain duplicate binders.
-- Do not descend under binders that bind the same variable as the one we're substituting for.
substituteDb
    :: Eq name
    => name -> Term tyname name uni fun () -> Term tyname name uni fun () -> Term tyname name uni fun ()
substituteDb varFor new = go where
    go = \case
         Var      () var          -> if var == varFor then new else Var () var
         TyAbs    () tyn ty body  -> TyAbs    () tyn ty (go body)
         LamAbs   () var ty body  -> LamAbs   () var ty (goUnder var body)
         Apply    () fun arg      -> Apply    () (go fun) (go arg)
         Constant () constant     -> Constant () constant
         TyInst   () fun arg      -> TyInst   () (go fun) arg
         Unwrap   () term         -> Unwrap   () (go term)
         IWrap    () pat arg term -> IWrap    () pat arg (go term)
         b@Builtin{}              -> b
         e@Error  {}              -> e
    goUnder var term = if var == varFor then term else go term

-- | Substitute a 'Type' for a type variable in a 'Term' that can contain duplicate binders.
-- Do not descend under binders that bind the same type variable as the one we're substituting for.
substTyInTerm
    :: Eq tyname
    => tyname -> Type tyname uni () -> Term tyname name uni fun () -> Term tyname name uni fun ()
substTyInTerm tn0 ty0 = go where
    go = \case
         v@Var{}                 -> v
         c@Constant{}            -> c
         b@Builtin{}             -> b
         TyAbs   () tn ty body   -> TyAbs   () tn ty (goUnder tn body)
         LamAbs  () var ty body  -> LamAbs  () var (goTy ty) (go body)
         Apply   () fun arg      -> Apply   () (go fun) (go arg)
         TyInst  () fun ty       -> TyInst  () (go fun) (goTy ty)
         Unwrap  () term         -> Unwrap  () (go term)
         IWrap   () pat arg term -> IWrap   () (goTy pat) (goTy arg) (go term)
         Error   () ty           -> Error   () (goTy ty)
    goUnder tn term = if tn == tn0 then term else go term
    goTy = substTyInTy tn0 ty0

-- | Substitute a 'Type' for a type variable in a 'Type' that can contain duplicate binders.
-- Do not descend under binders that bind the same type variable as the one we're substituting for.
substTyInTy
    :: Eq tyname
    => tyname -> Type tyname uni () -> Type tyname uni () -> Type tyname uni ()
substTyInTy tn0 ty0 = go where
    go = \case
         TyVar    () tn      -> if tn == tn0 then ty0 else TyVar () tn
         TyFun    () ty1 ty2 -> TyFun    () (go ty1) (go ty2)
         TyIFix   () ty1 ty2 -> TyIFix   () (go ty1) (go ty2)
         TyApp    () ty1 ty2 -> TyApp    () (go ty1) (go ty2)
         TyForall () tn k ty -> TyForall () tn k (goUnder tn ty)
         TyLam    () tn k ty -> TyLam    () tn k (goUnder tn ty)
         bt@TyBuiltin{}      -> bt
    goUnder tn ty = if tn == tn0 then ty else go ty

-- FIXME: make sure that the specification is up to date and that this matches.
-- | The computing part of the CK machine. Rules are as follows:
--
-- > s ▷ {M A}      ↦ s , {_ A}        ▷ M
-- > s ▷ [M N]      ↦ s , [_ N]        ▷ M
-- > s ▷ wrap α A M ↦ s , (wrap α S _) ▷ M
-- > s ▷ unwrap M   ↦ s , (unwrap _)   ▷ M
-- > s ▷ abs α K M  ↦ s ◁ abs α K M
-- > s ▷ lam x A M  ↦ s ◁ lam x A M
-- > s ▷ builtin bn ↦ s ◁ builtin bn (arity bn) (arity bn) [] []
-- > s ▷ con cn     ↦ s ◁ con cn
-- > s ▷ error A    ↦ ◆
(|>)
    :: (GShow uni, GEq uni, Ix fun)
    => Context uni fun -> Term TyName Name uni fun () -> CkM uni fun (Term TyName Name uni fun ())
stack |> TyInst  _ fun ty        = FrameTyInstArg ty  : stack |> fun
stack |> Apply   _ fun arg       = FrameApplyArg arg  : stack |> fun
stack |> IWrap   _ pat arg term  = FrameIWrap pat arg : stack |> term
stack |> Unwrap  _ term          = FrameUnwrap        : stack |> term
stack |> TyAbs   _ tn k term     = stack <| VTyAbs tn k term
stack |> LamAbs  _ name ty body  = stack <| VLamAbs name ty body
stack |> Builtin _ bn            = do
    BuiltinRuntime _ arity _ _ <- asksM $ lookupBuiltin bn . ckEnvRuntime
    stack <| VBuiltin bn arity arity [] []
stack |> c@Constant{}          = stack <| VCon c
_     |> _err@Error{}          =
    throwingWithCause _EvaluationError (UserEvaluationError CkEvaluationFailure) $ Nothing
_     |> _var@Var{}            =
    throwingWithCause _MachineError OpenTermEvaluatedMachineError $ Nothing


-- FIXME: make sure that the specification is up to date and that this matches.
-- | The returning part of the CK machine. Rules are as follows:
--
-- > s , {_ A}           ◁ abs α K M  ↦ s         ▷ {A/α}M
-- > s , [_ N]           ◁ V          ↦ s , [V _] ▷ N
-- > s , [(lam x A M) _] ◁ V          ↦ s         ▷ [V/x]M
-- > s , {_ A}           ◁ F          ↦ s ◁ {F A}  -- Partially instantiated built-in application.
-- > s , [F _]           ◁ V          ↦ s ◁ [F V]  -- Partially saturated built-in application.
-- > s , [F _]           ◁ V          ↦ s ◁ W      -- Fully saturated constant, [F V] ~> W.
-- > s , (wrap α S _)    ◁ V          ↦ s ◁ wrap α S V
-- > s , (unwrap _)      ◁ wrap α A V ↦ s ◁ V
(<|)
    :: (GShow uni, GEq uni, Ix fun)
    => Context uni fun -> CkValue uni fun -> CkM uni fun (Term TyName Name uni fun ())
[]                         <| val     = pure $ ckValueToTerm () val
FrameTyInstArg ty  : stack <| fun     = instantiateEvaluate stack ty fun
FrameApplyArg arg  : stack <| fun     = FrameApplyFun fun : stack |> arg
FrameApplyFun fun  : stack <| arg     = applyEvaluate stack fun arg
FrameIWrap pat arg : stack <| value   = stack <| VIWrap pat arg value
FrameUnwrap        : stack <| wrapped = case wrapped of
    VIWrap _ _ term -> stack <| term
    _term           -> throwingWithCause _MachineError NonWrapUnwrappedMachineError $ Nothing

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

-- | Instantiate a term with a type and proceed.
-- In case of 'TyAbs' just ignore the type. Otherwise check if the term is an
-- iterated application of a 'Builtin' to a list of 'Value's and, if succesful,
-- apply the term to the type via 'TyInst'.
instantiateEvaluate
    :: (GShow uni, GEq uni, Ix fun)
    => Context uni fun
    -> Type TyName uni ()
    -> CkValue uni fun
    -> CkM uni fun (Term TyName Name uni fun ())
instantiateEvaluate stack ty (VTyAbs tn _k body) = stack |> (substTyInTerm tn ty body) -- No kind check - too expensive at run time.
instantiateEvaluate stack ty val@(VBuiltin bn arity0 arity tys args) =
    case arity of
      []             -> throwingWithCause _MachineError EmptyBuiltinArityMachineError $ Just val
                                                                                 -- Should be impossible: see instantiateEvaluate.
      TermArg:_      -> throwingWithCause _MachineError BuiltinTermArgumentExpectedMachineError $ Just val'
                        where val' = VBuiltin bn arity0 arity (tys++[ty]) args   -- Reconstruct the bad application
      TypeArg:[]     -> applyBuiltin stack bn args                           -- Final argument is a type argument
      TypeArg:arity' -> stack <| VBuiltin bn arity0 arity' (tys++[ty]) args      -- More arguments expected
instantiateEvaluate _ _ val =
    throwingWithCause _MachineError NonPolymorphicInstantiationMachineError $ Just val

-- | Apply a function to an argument and proceed.
-- If the function is not a 'LamAbs', then 'Apply' it to the argument and view this
-- as an iterated application of a 'Builtin' to a list of 'Value's.
-- If succesful, proceed with either this same term or with the result of the computation
-- depending on whether 'Builtin' is saturated or not.
applyEvaluate
    :: (GShow uni, GEq uni, Ix fun)
    => Context uni fun
    -> CkValue uni fun
    -> CkValue uni fun
    -> CkM uni fun (Term TyName Name uni fun ())
applyEvaluate stack (VLamAbs name _ body) arg = stack |> substituteDb name (ckValueToTerm () arg) body
applyEvaluate stack val@(VBuiltin bn arity0 arity tyargs args) arg = do
    case arity of
      []             -> throwingWithCause _MachineError EmptyBuiltinArityMachineError $ Just val
                                                                                    -- Should be impossible: see instantiateEvaluate.
      TypeArg:_      -> throwingWithCause _MachineError UnexpectedBuiltinTermArgumentMachineError $ Just val'
                        where val' = VBuiltin bn arity0 arity tyargs (args++[arg])  -- Reconstruct the bad application
      TermArg:[]     -> applyBuiltin stack bn (args ++ [arg])                   -- 'arg' was the final argument
      TermArg:arity' -> stack <| VBuiltin bn arity0 arity' tyargs (args++[arg])     -- More arguments expected
applyEvaluate _ val _ = throwingWithCause _MachineError NonFunctionalApplicationMachineError $ Just val

-- | Apply a (static or dynamic) built-in function to some arguments
applyBuiltin
    :: (GShow uni, GEq uni, Ix fun)
    => Context uni fun
    -> fun
    -> [CkValue uni fun]
    -> CkM uni fun (Term TyName Name uni fun ())
applyBuiltin stack bn args = do
    BuiltinRuntime sch _ f exF <- asksM $ lookupBuiltin bn . ckEnvRuntime
    result <- applyTypeSchemed bn sch f exF args
    case result of
        EvaluationSuccess t -> stack <| t
        EvaluationFailure ->
            throwingWithCause _EvaluationError (UserEvaluationError CkEvaluationFailure) $ Nothing

-- | Evaluate a term using the CK machine. May throw a 'CkEvaluationException'.
evaluateCk
    :: (GShow uni, GEq uni, Ix fun)
    => BuiltinsRuntime fun (CkValue uni fun)
    -> Term TyName Name uni fun ()
    -> Either (CkEvaluationException uni fun) (Term TyName Name uni fun ())
evaluateCk runtime term = runReaderT ([] |> term) $ CkEnv runtime

-- | Evaluate a term using the CK machine. May throw a 'CkEvaluationException'.
unsafeEvaluateCk
    :: ( GShow uni, GEq uni, Closed uni
       , Typeable uni, Typeable fun, uni `Everywhere` PrettyConst
       , Pretty fun, Ix fun
       )
    => BuiltinsRuntime fun (CkValue uni fun)
    -> Term TyName Name uni fun ()
    -> EvaluationResult (Term TyName Name uni fun ())
unsafeEvaluateCk runtime = either throw id . extractEvaluationResult . evaluateCk runtime
