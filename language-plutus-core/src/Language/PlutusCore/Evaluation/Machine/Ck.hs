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
    , CkValue (..)
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
import           Language.PlutusCore.Evaluation.Machine.ExMemory            (Plain)

import           Language.PlutusCore.Evaluation.Result
import           Language.PlutusCore.MkPlc                                  (mkIterApp, mkIterInst)
import           Language.PlutusCore.Name
import           Language.PlutusCore.Pretty                                 (PrettyConfigPlc, PrettyConst)
import           Language.PlutusCore.Universe

import           Data.Array

infix 4 |>, <|

-- | The CK machine throws this error when it encounters a 'DynBuiltinName'.
data NoDynamicBuiltinNamesMachineError
    = NoDynamicBuiltinNamesMachineError DynamicBuiltinName
    deriving (Show, Eq)

-- | The CK machine-specific 'EvaluationException'.
type CkEvaluationException uni =
    EvaluationException NoDynamicBuiltinNamesMachineError () (CkValue uni)


data CkValue uni =
    VCon (Term TyName Name uni ())  -- TODO: Really want a constant here.
  | VTyAbs TyName (Kind ()) (Term TyName Name uni ())
  | VLamAbs Name (Type TyName uni ()) (Term TyName Name uni ())
  | VIWrap (Type TyName uni ()) (Type TyName uni ()) (CkValue uni)
  | VBuiltin
      BuiltinName
      Int                   -- Number of arguments to be provided (both types and terms)
      [Type TyName uni ()]  -- The types the builtin is to be instantiated at.
                            -- We need these to construct a term if the machine is returning a stuck partial application.
      [CkValue uni]         -- Arguments we've computed so far.
      deriving (Show, Eq)   -- Eq is just for tests.

instance (Closed uni, GShow uni, uni `Everywhere` PrettyConst) => PrettyBy PrettyConfigPlc (CkValue uni) where
    prettyBy cfg = prettyBy cfg . ckValueToTerm

type instance UniOf (CkValue uni) = uni

instance FromConstant (CkValue uni) where
    fromConstant = VCon . fromConstant

instance AsConstant (CkValue uni) where
    asConstant (VCon term) = asConstant term
    asConstant _           = Nothing

instance SpendBudget (CkM uni) (CkValue uni) where
    builtinCostParams = pure defaultCostModel
    spendBudget _key _budget = pure ()

instance ToExMemory (CkValue uni) where
    toExMemory _ = 0

mkBuiltinApp :: BuiltinName -> [Type TyName uni ()] -> [Plain Term uni] -> Plain Term uni
mkBuiltinApp bn tys args = mkIterApp () (mkIterInst () (Builtin () bn) tys) args

ckValueToTerm :: CkValue uni -> Plain Term uni
ckValueToTerm = \case
    VCon t                 -> t
    VTyAbs tn k body       -> TyAbs () tn k body
    VLamAbs name ty body   -> LamAbs () name ty body
    VIWrap t1 t2 body      -> IWrap () t1 t2 (ckValueToTerm body)
    VBuiltin bn _ tys args -> mkBuiltinApp bn tys (fmap ckValueToTerm args)

type CkM uni = Either (CkEvaluationException uni)

getArgsCount :: BuiltinName -> CkM uni Int
getArgsCount (StaticBuiltinName name) =
    pure $ builtinNameAritiesIncludingTypes ! name
getArgsCount (DynBuiltinName name) =
    throwingWithCause _MachineError (OtherMachineError $ NoDynamicBuiltinNamesMachineError name) Nothing

data Frame uni
    = FrameApplyFun (CkValue uni)                           -- ^ @[V _]@
    | FrameApplyArg (Plain Term uni)                        -- ^ @[_ N]@
    | FrameTyInstArg (Type TyName uni ())                   -- ^ @{_ A}@
    | FrameUnwrap                                           -- ^ @(unwrap _)@
    | FrameIWrap (Type TyName uni ()) (Type TyName uni ())  -- ^ @(iwrap A B _)@

type Context uni = [Frame uni]

instance Pretty NoDynamicBuiltinNamesMachineError where
    pretty (NoDynamicBuiltinNamesMachineError name) =
        "The CK machine doesn't support dynamic extensions to the set of built-in names (found \"" <> pretty name <>  "\")."

-- | Substitute a 'Value' for a variable in a 'Term' that can contain duplicate binders.
-- Do not descend under binders that bind the same variable as the one we're substituting for.
substituteDb
    :: Eq name
    => name -> Value tyname name uni a -> Term tyname name uni a -> Term tyname name uni a
substituteDb varFor new = go where
    go = \case
     Var      ann var          -> if var == varFor then new else Var ann var
     TyAbs    ann tyn ty body  -> TyAbs ann tyn ty (go body)
     LamAbs   ann var ty body  -> LamAbs ann var ty (goUnder var body)
     Apply    ann fun arg      -> Apply ann (go fun) (go arg)
     Constant ann constant     -> Constant ann constant
     Builtin  ann bi           -> Builtin ann bi
     TyInst   ann fun arg      -> TyInst ann (go fun) arg
     Unwrap   ann term         -> Unwrap ann (go term)
     IWrap    ann pat arg term -> IWrap ann pat arg (go term)
     Error    ann ty           -> Error ann ty

    goUnder var term = if var == varFor then term else go term


-- TODO: Fix these if we decide to use this
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
    :: (Closed uni, GShow uni, GEq uni, DefaultUni <: uni)
    => Context uni -> Plain Term uni -> CkM uni (Plain Term uni)
stack |> TyInst  _ fun ty        = FrameTyInstArg ty  : stack |> fun
stack |> Apply   _ fun arg       = FrameApplyArg arg  : stack |> fun
stack |> IWrap   _ pat arg term  = FrameIWrap pat arg : stack |> term
stack |> Unwrap  _ term          = FrameUnwrap        : stack |> term
stack |> TyAbs   _ tn k body     = stack <| VTyAbs tn k body
stack |> LamAbs  _ name ty body  = stack <| VLamAbs name ty body
stack |> Builtin _ bn            = do
                                    count <- getArgsCount bn
                                    stack <| VBuiltin bn count [] []
stack |> c@Constant{}  = stack <| VCon c
_     |> _err@Error{}          =
           throwingWithCause _EvaluationError (UserEvaluationError ()) $ Nothing   -- Just err
_     |> _var@Var{}            =
           throwingWithCause _MachineError OpenTermEvaluatedMachineError $ Nothing -- Just var


-- TODO: Fix these if we decide to use this
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
    :: (Closed uni, GShow uni, GEq uni, DefaultUni <: uni)
    => Context uni -> CkValue uni -> CkM uni (Plain Term uni)
[]                         <| val     = pure $ ckValueToTerm val
FrameTyInstArg ty  : stack <| fun     = instantiateEvaluate stack ty fun
FrameApplyArg arg  : stack <| fun     = FrameApplyFun fun : stack |> arg
FrameApplyFun fun  : stack <| arg     = applyEvaluate stack fun arg
FrameIWrap pat arg : stack <| value   = stack <| VIWrap pat arg value
FrameUnwrap        : stack <| wrapped =
    case wrapped of
      VIWrap _ _ term -> stack <| term
      _term           -> throwingWithCause _MachineError NonWrapUnwrappedMachineError $ Nothing -- Just term

-- | Instantiate a term with a type and proceed.
-- In case of 'TyAbs' just ignore the type. Otherwise check if the term is an
-- iterated application of a 'BuiltinName' to a list of 'Value's and, if succesful,
-- apply the term to the type via 'TyInst'.
instantiateEvaluate
    :: (Closed uni, GShow uni, GEq uni, DefaultUni <: uni)
    => Context uni
    -> Type TyName uni ()
    -> CkValue uni
    -> CkM uni (Plain Term uni)
instantiateEvaluate stack _ (VTyAbs _ _ body) = stack |> body
instantiateEvaluate stack ty (VBuiltin bn count tys args) =
    stack <| VBuiltin bn (count-1) (ty:tys) args
    -- FIXME: What if count = 0, ie the final argument is a type?  Also, what if count < 0?
instantiateEvaluate _ _ val =
    throwingWithCause _MachineError NonPolymorphicInstantiationMachineError $ Just val

{-
    | isJust $ termAsPrimIterApp fun = stack <| fun -- Discard type
    | otherwise                      =
          throwingWithCause _MachineError NonPolymorphicInstantiationMachineError $ Just fun
-}
-- | Apply a function to an argument and proceed.
-- If the function is not a 'LamAbs', then 'Apply' it to the argument and view this
-- as an iterated application of a 'BuiltinName' to a list of 'Value's.
-- If succesful, proceed with either this same term or with the result of the computation
-- depending on whether 'BuiltinName' is saturated or not.
applyEvaluate
    :: (Closed uni, GShow uni, GEq uni, DefaultUni <: uni)
    => Context uni
    -> CkValue uni
    -> CkValue uni
    -> CkM uni (Plain Term uni)
applyEvaluate stack (VLamAbs name _ body) arg  = stack |> substituteDb name (ckValueToTerm arg) body
applyEvaluate stack val@(VBuiltin bn count tyargs args) arg = do
    let args' = arg:args
        count' = count - 1
    if count' /= 0 -- What if count < 0 ?
        then stack <| VBuiltin bn count' tyargs args'
        else do
            res <- applyBuiltinName bn (reverse args')
            case res of
                EvaluationSuccess v -> stack <| v
                EvaluationFailure ->
                    throwingWithCause _EvaluationError (UserEvaluationError ()) $ Just val
applyEvaluate _ val _ =throwingWithCause _MachineError NonFunctionalApplicationMachineError $ Just val

applyBuiltinName
    :: (GShow uni, GEq uni, DefaultUni <: uni)
    => BuiltinName
    -> [CkValue uni]
    -> CkM uni (EvaluationResult (CkValue uni))
applyBuiltinName (DynBuiltinName name) _args =
    throwingWithCause _MachineError (OtherMachineError $ NoDynamicBuiltinNamesMachineError name) Nothing
applyBuiltinName (StaticBuiltinName name) args =
    applyStaticBuiltinName name args


-- | Evaluate a term using the CK machine. May throw a 'CkEvaluationException'.
-- This differs from the spec version: we do not have the following rule:
--
-- > s , {_ A} ◁ F ↦ s ◁ W  -- Fully saturated constant, {F A} ~> W.
--
-- The reason for that is that the operational semantics of constant applications is
-- unaffected by types as it supports full type erasure, hence @{F A}@ can never compute
-- if @F@ does not compute, so we simply do not introduce a rule that can't possibly fire.
evaluateCk
    :: (Closed uni, GShow uni, GEq uni, DefaultUni <: uni)
    => Plain Term uni -> Either (CkEvaluationException uni) (Plain Term uni)
evaluateCk term = [] |> term

-- | Evaluate a term using the CK machine. May throw a 'CkEvaluationException'.
unsafeEvaluateCk
    :: (GShow uni, GEq uni, DefaultUni <: uni, Closed uni
       , Typeable uni, uni `Everywhere` PrettyConst
       )
    => Plain Term uni -> EvaluationResult (Plain Term uni)
unsafeEvaluateCk = either throw id . extractEvaluationResult . evaluateCk
