-- | The CK machine.

{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE UndecidableInstances  #-}

module Language.PlutusCore.Evaluation.Machine.Ck
    ( EvaluationResult (..)
    , CkEvaluationException
    , CkM
    , evaluateCk
    , unsafeEvaluateCk
    ) where

import           PlutusPrelude

import           Language.PlutusCore.Constant
import           Language.PlutusCore.Core
import           Language.PlutusCore.Evaluation.Machine.ExBudgeting
import           Language.PlutusCore.Evaluation.Machine.ExBudgetingDefaults (defaultCostModel)
import           Language.PlutusCore.Evaluation.Machine.Exception
import           Language.PlutusCore.Evaluation.Result
import           Language.PlutusCore.Name
import           Language.PlutusCore.Pretty                                 (PrettyConfigPlc, PrettyConst)
import           Language.PlutusCore.Universe

import           Data.Array

infix 4 |>, <|

data CkValue uni ann =
    VCon (Term TyName Name uni ann)  -- TODO: Really want a constant here.
  | VTyAbs TyName (Kind ann) (Term TyName Name uni ann)
  | VLamAbs Name (Type TyName uni ann) (Term TyName Name uni ann)
  | VIWrap (Type TyName uni ann) (Type TyName uni ann) (CkValue uni ann)
  | VBuiltin
      BuiltinName
      Arity                -- Sorts of arguments to be provided (both types and terms): *don't change this*.
      Arity                -- A copy of the arity used for checking applications/instantiatons: see [Note: Arities in VBuiltin]
      [Type TyName uni ann] -- The types the builtin is to be instantiated at.
                           -- We need these to construct a term if the machine is returning a stuck partial application.
      [CkValue uni ann]        -- Arguments we've computed so far.
    deriving (Show, Eq)   -- Eq is just for tests.

mkBuiltinApplication :: ann -> BuiltinName -> Arity -> [Type TyName uni ann] -> [Term TyName Name uni ann] -> Term TyName Name uni ann
mkBuiltinApplication ann bn arity0 tys0 args0 =
  go arity0 tys0 args0 (Builtin ann bn)
    where go arity tys args term =
              case (arity, args, tys) of
                ([], [], [])                        -> term   -- We've got to the end and successfully constructed the entire application
                (TermArg:arity', arg:args', _)      -> go arity' tys args' (Apply ann term arg)  -- got an expected term argument
                (TermArg:_,      [],       ty:_)    -> TyInst ann term ty                        -- term expected, type found
                (TypeArg:arity', _,        ty:tys') -> go arity' tys' args (TyInst ann term ty)  -- got an expected type argument
                (TypeArg:_,      arg:_,    [])      -> Apply ann term arg                        -- type expected, term found
                _                                   -> term                                     -- something else, including partial application

ckValueToTerm :: ann -> CkValue uni ann -> Term TyName Name uni ann
ckValueToTerm ann = \case
    VCon t                           -> t
    VTyAbs   tn k body               -> TyAbs ann tn k body
    VLamAbs  name ty body            -> LamAbs ann name ty body
    VIWrap   ty1 ty2 val             -> IWrap ann ty1 ty2 $ ckValueToTerm ann val
    VBuiltin bn arity0 _ tyargs args -> mkBuiltinApplication ann bn arity0 tyargs (fmap (ckValueToTerm ann) args)
    {- We only discharge a value when (a) it's being returned by the machine,
       or (b) it's needed for an error message.  When we're discharging VBuiltin
       we use arity0 to get the type and term arguments into the right sequence. -}

instance (Closed uni, GShow uni, uni `Everywhere` PrettyConst) => PrettyBy PrettyConfigPlc (CkValue uni ()) where
    prettyBy cfg = prettyBy cfg . ckValueToTerm ()

-- | The CK machine throws this error when it encounters a 'DynBuiltinName'.
data NoDynamicBuiltinNamesMachineError
    = NoDynamicBuiltinNamesMachineError DynamicBuiltinName
    deriving (Show, Eq)

-- | The CK machine-specific 'EvaluationException'.
type CkEvaluationException uni =
    EvaluationException NoDynamicBuiltinNamesMachineError () (CkValue uni ())

type CkM uni = Either (CkEvaluationException uni)

instance SpendBudget (CkM uni) (CkValue uni ()) where
    builtinCostParams = pure defaultCostModel
    spendBudget _key _budget = pure ()

type instance UniOf (CkValue uni ann) = uni

instance FromConstant (CkValue uni ()) where
    fromConstant = VCon . fromConstant

instance AsConstant (CkValue uni ann) where
    asConstant (VCon term) = asConstant term
    asConstant _           = Nothing

instance ToExMemory (CkValue uni ann) where
    toExMemory _ = 0



data Frame uni ann
    = FrameApplyFun (CkValue uni ann)                         -- ^ @[V _]@
    | FrameApplyArg (Term TyName Name uni ann)                -- ^ @[_ N]@
    | FrameTyInstArg (Type TyName uni ann)                    -- ^ @{_ A}@
    | FrameUnwrap                                             -- ^ @(unwrap _)@
    | FrameIWrap (Type TyName uni ann) (Type TyName uni ann)  -- ^ @(iwrap A B _)@

type Context uni = [Frame uni ()]

instance Pretty NoDynamicBuiltinNamesMachineError where
    pretty (NoDynamicBuiltinNamesMachineError name) =
        "The CK machine doesn't support dynamic extensions to the set of built-in names (found \"" <> pretty name <>  "\")."

-- | Substitute a 'Term' for a variable in a 'Term' that can contain duplicate binders.
-- Do not descend under binders that bind the same variable as the one we're substituting for.
substituteDb
    :: Eq name
    => name -> Term tyname name uni ann -> Term tyname name uni ann -> Term tyname name uni ann
substituteDb varFor new = go where
    go = \case
      Var      ann var          -> if var == varFor then new else Var ann var
      TyAbs    ann tyn ty body  -> TyAbs    ann tyn ty (go body)
      LamAbs   ann var ty body  -> LamAbs   ann var ty (goUnder var body)
      Apply    ann fun arg      -> Apply    ann (go fun) (go arg)
      Constant ann constant     -> Constant ann constant
      Builtin  ann bi           -> Builtin  ann bi
      TyInst   ann fun arg      -> TyInst   ann (go fun) arg
      Unwrap   ann term         -> Unwrap   ann (go term)
      IWrap    ann pat arg term -> IWrap    ann pat arg (go term)
      Error    ann ty           -> Error    ann ty

    goUnder var term = if var == varFor then term else go term

arityOf :: BuiltinName -> CkM uni Arity
arityOf (StaticBuiltinName name) =
    pure $ builtinNameArities ! name
arityOf (DynBuiltinName _name) = do
    --DynamicBuiltinNameMeaning sch _ _ <- undefined -- lookupDynamicBuiltinName name
    undefined -- pure $ getArity sch
-- TODO: have a table of dynamic arities so that we don't have to do this computation every time.

-- FIXME: update this for the current strategy
-- | The computing part of the CK machine. Rules are as follows:
--
-- > s ▷ {M A}      ↦ s , {_ A}        ▷ M
-- > s ▷ [M N]      ↦ s , [_ N]        ▷ M
-- > s ▷ wrap α A M ↦ s , (wrap α S _) ▷ M
-- > s ▷ unwrap M   ↦ s , (unwrap _)   ▷ M
-- > s ▷ abs α K M  ↦ s ◁ abs α K M
-- > s ▷ lam x A M  ↦ s ◁ lam x A M
-- > s ▷ con cn     ↦ s ◁ con cn
-- > s ▷ error A    ↦ ◆
(|>)
    :: (GShow uni, GEq uni, DefaultUni <: uni)
    => Context uni -> Term TyName Name uni () -> CkM uni (Term TyName Name uni ())
stack |> TyInst  _ fun ty        = FrameTyInstArg ty  : stack |> fun
stack |> Apply   _ fun arg       = FrameApplyArg arg  : stack |> fun
stack |> IWrap   _ pat arg term  = FrameIWrap pat arg : stack |> term
stack |> Unwrap  _ term          = FrameUnwrap        : stack |> term
stack |> TyAbs   _ tn k term     = stack <| VTyAbs tn k term
stack |> LamAbs  _ name ty body  = stack <| VLamAbs name ty body
stack |> Builtin _ bn            = do
                                    arity <- arityOf bn
                                    stack <| VBuiltin bn arity arity [] []
stack |> c@Constant{}          = stack <| VCon c
_     |> _err@Error{}          =
    throwingWithCause _EvaluationError (UserEvaluationError ()) $ Nothing
_     |> _var@Var{}            =
    throwingWithCause _MachineError OpenTermEvaluatedMachineError $ Nothing
-- | The returning part of the CK machine. Rules are as follows:
--
-- > s , {_ A}           ◁ abs α K M  ↦ s         ▷ M
-- > s , [_ N]           ◁ V          ↦ s , [V _] ▷ N
-- > s , [(lam x A M) _] ◁ V          ↦ s         ▷ [V/x]M
-- > s , {_ A}           ◁ F          ↦ s ◁ {F A}  -- Partially saturated constant.
-- > s , [F _]           ◁ V          ↦ s ◁ [F V]  -- Partially saturated constant.
-- > s , [F _]           ◁ V          ↦ s ◁ W      -- Fully saturated constant, [F V] ~> W.
-- > s , (wrap α S _)    ◁ V          ↦ s ◁ wrap α S V
-- > s , (unwrap _)      ◁ wrap α A V ↦ s ◁ V
(<|)
    :: (GShow uni, GEq uni, DefaultUni <: uni)
    => Context uni -> CkValue uni () -> CkM uni (Term TyName Name uni ())
[]                         <| val     = pure $ ckValueToTerm () val
FrameTyInstArg ty  : stack <| fun     = instantiateEvaluate stack ty fun
FrameApplyArg arg  : stack <| fun     = FrameApplyFun fun : stack |> arg
FrameApplyFun fun  : stack <| arg     = applyEvaluate stack fun arg
FrameIWrap pat arg : stack <| value   = stack <| VIWrap pat arg value
FrameUnwrap        : stack <| wrapped = case wrapped of
    VIWrap _ _ term -> stack <| term
    _term           -> throwingWithCause _MachineError NonWrapUnwrappedMachineError $ Nothing

-- | Instantiate a term with a type and proceed.
-- In case of 'TyAbs' just ignore the type. Otherwise check if the term is an
-- iterated application of a 'BuiltinName' to a list of 'Value's and, if succesful,
-- apply the term to the type via 'TyInst'.
instantiateEvaluate
    :: (GShow uni, GEq uni, DefaultUni <: uni)
    => Context uni
    -> Type TyName uni ()
    -> CkValue uni ()
    -> CkM uni (Term TyName Name uni ())
instantiateEvaluate stack _  (VTyAbs _ _ body) = stack |> body
instantiateEvaluate stack ty val@(VBuiltin bn arity0 arity tys args) =
    case arity of
      []        -> throwingWithCause _MachineError EmptyBuiltinArityMachineError $ Just val
                -- Should be impossible: see instantiateEvaluate.
      TermArg:_      -> throwingWithCause _MachineError UnexpectedBuiltinInstantiationMachineError $ Just val'
                        where val' = VBuiltin bn arity0 arity (tys++[ty]) args -- reconstruct the bad application
      TypeArg:arity' ->
          case arity' of
            [] -> applyBuiltinName stack bn args  -- Final argument is a type argument
            _  -> stack <| VBuiltin bn arity0 arity' (tys++[ty]) args -- More arguments expected
instantiateEvaluate _ _ val =
    throwingWithCause _MachineError NonPolymorphicInstantiationMachineError $ Just val

-- | Apply a function to an argument and proceed.
-- If the function is not a 'LamAbs', then 'Apply' it to the argument and view this
-- as an iterated application of a 'BuiltinName' to a list of 'Value's.
-- If succesful, proceed with either this same term or with the result of the computation
-- depending on whether 'BuiltinName' is saturated or not.
applyEvaluate
    :: (GShow uni, GEq uni, DefaultUni <: uni)
    => Context uni
    -> CkValue uni ()
    -> CkValue uni ()
    -> CkM uni (Term TyName Name uni ())
applyEvaluate stack (VLamAbs name _ body) arg = stack |> substituteDb name (ckValueToTerm () arg) body
applyEvaluate stack val@(VBuiltin bn arity0 arity tyargs args) arg = do
    case arity of
      []        -> throwingWithCause _MachineError EmptyBuiltinArityMachineError $ Just val
                -- Should be impossible: see instantiateEvaluate.
      TypeArg:_ -> throwingWithCause _MachineError UnexpectedBuiltinTermArgumentMachineError $ Just val'
                   where val' = VBuiltin bn arity0 arity tyargs (args++[arg]) -- reconstruct the bad application
      TermArg:arity' -> do
          let args' = args ++ [arg]
          case arity' of
            [] -> applyBuiltinName stack bn args' -- 'arg' was the final argument
            _  -> stack <| VBuiltin bn arity0 arity' tyargs args' -- More arguments expected
applyEvaluate _ val _ = throwingWithCause _MachineError NonFunctionalApplicationMachineError $ Just val

applyBuiltinName
    :: (GShow uni, GEq uni, DefaultUni <: uni)
    => Context uni
    -> BuiltinName
    -> [CkValue uni ()]
    -> CkM uni (Term TyName Name uni ())
applyBuiltinName _ (DynBuiltinName name) _args =
    throwingWithCause _MachineError (OtherMachineError $ NoDynamicBuiltinNamesMachineError name) Nothing
applyBuiltinName stack (StaticBuiltinName name) args = do
    result <- applyStaticBuiltinName name args
    case result of
      EvaluationSuccess t -> stack <| t
      EvaluationFailure ->
          throwingWithCause _EvaluationError (UserEvaluationError ()) $ Nothing

-- | Evaluate a term using the CK machine. May throw a 'CkEvaluationException'.
-- This differs from the spec version: we do not have the following rule:
--
-- > s , {_ A} ◁ F ↦ s ◁ W  -- Fully saturated constant, {F A} ~> W.
--
-- The reason for that is that the operational semantics of constant applications is
-- unaffected by types as it supports full type erasure, hence @{F A}@ can never compute
-- if @F@ does not compute, so we simply do not introduce a rule that can't possibly fire.
evaluateCk
    :: (GShow uni, GEq uni, DefaultUni <: uni)
    => Term TyName Name uni () -> Either (CkEvaluationException uni) (Term TyName Name uni ())
evaluateCk term = [] |> term

-- | Evaluate a term using the CK machine. May throw a 'CkEvaluationException'.
unsafeEvaluateCk
    :: ( GShow uni, GEq uni, DefaultUni <: uni, Closed uni
       , Typeable uni, uni `Everywhere` PrettyConst
       )
    => Term TyName Name uni () -> EvaluationResult (Term TyName Name uni ())
unsafeEvaluateCk = either throw id . extractEvaluationResult . evaluateCk
