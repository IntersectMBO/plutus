{-# LANGUAGE TypeApplications  #-}

-- | The CK machine.

{-# LANGUAGE OverloadedStrings #-}

module Language.PlutusCore.Evaluation.CkMachine
    ( CkMachineException
    , EvaluationResult (..)
    , EvaluationResultDef
    , applyEvaluateCkBuiltinName
    , evaluatorCk
    , readKnownCk
    , evaluateCk
    , runCk
    ) where

import           Language.PlutusCore.Constant.Apply
import           Language.PlutusCore.Constant.Dynamic.Instances
import           Language.PlutusCore.Constant.Typed
import           Language.PlutusCore.Constant.Universe
import           Language.PlutusCore.Error
import           Language.PlutusCore.Evaluation.MachineException
import           Language.PlutusCore.Evaluation.Result
import           Language.PlutusCore.Name
import           Language.PlutusCore.Type
import           Language.PlutusCore.View
import           PlutusPrelude

import           Control.Monad.Reader
import           Data.Functor.Identity
import qualified Data.Map                                        as Map
import           Data.Text                                       (Text)

import qualified Data.ByteString.Lazy                            as BSL
import           Language.PlutusCore.Constant.DefaultUni
import           Language.PlutusCore.StdLib.Data.Unit

instance Pretty BSL.ByteString where
    pretty _ = "<bytesting>"

test1 :: EvaluationResult (Either Text (Shallow Integer, Bool))
test1 = readKnownCk @_ @DefaultUni . makeKnown $ (Shallow (5 :: Integer), True)

test :: EvaluationResult (Either Text ((Shallow Integer, ()), (Char, Bool)))
test = readKnownCk @_ @DefaultUni $ makeKnown ((Shallow (5 :: Integer), ()), ('a', True))

test2 :: EvaluationResult (Either Text ())
test2 = readKnownCk @() @DefaultUni unitval


infix 4 |>, <|

-- | The CK machine-specific 'MachineException'.
type CkMachineException uni = MachineException uni UnknownDynamicBuiltinNameError

-- | The environment the CEK machine runs in.
type CkEnv uni = NameMeanings uni

-- | The monad the CEK machine runs in.
type CkM uni = Reader (CkEnv uni)

data Frame uni
    = FrameApplyFun (Value TyName Name uni ())                 -- ^ @[V _]@
    | FrameApplyArg (Term TyName Name uni ())                  -- ^ @[_ N]@
    | FrameTyInstArg (Type TyName uni ())                      -- ^ @{_ A}@
    | FrameUnwrap                                              -- ^ @(unwrap _)@
    | FrameIWrap () (Type TyName uni ()) (Type TyName uni ())  -- ^ @(iwrap A B _)@

type Context uni = [Frame uni]

runCkM :: NameMeanings uni -> CkM uni a -> a
runCkM = flip runReader

-- | Throw a 'CkMachineException'. This function is needed, because it constrains 'MachinerError'
-- to be parametrized by a 'NoDynamicBuiltinNamesError' which is required in order to disambiguate
-- @throw .* MachineException@.
throwCkMachineException
    :: Evaluable uni
    => MachineError uni UnknownDynamicBuiltinNameError -> Term TyName Name uni () -> a
throwCkMachineException = throw .* MachineException

-- | Look up a 'DynamicBuiltinName' in the environment.
lookupDynamicBuiltinName
    :: forall uni. Evaluable uni => DynamicBuiltinName -> CkM uni (NameMeaning uni)
lookupDynamicBuiltinName dynName = do
    NameMeanings means <- ask
    case Map.lookup dynName means of
        Nothing   -> throw $ MachineException @uni err term where
            err  = OtherMachineError $ UnknownDynamicBuiltinNameErrorE dynName
            term = Builtin () $ DynBuiltinName () dynName
        Just mean -> pure mean

-- | Substitute a 'Value' for a variable in a 'Term' that can contain duplicate binders.
-- Do not descend under binders that bind the same variable as the one we're substituting for.
substituteDb
    :: Eq (name a)
    => name a -> Value tyname name uni a -> Term tyname name uni a -> Term tyname name uni a
substituteDb varFor new = go where
    go (Var ann var)            = if var == varFor then new else Var ann var
    go (TyAbs ann tyn ty body)  = TyAbs ann tyn ty (go body)
    go (LamAbs ann var ty body) = LamAbs ann var ty (goUnder var body)
    go (Apply ann fun arg)      = Apply ann (go fun) (go arg)
    go (Constant ann constant)  = Constant ann constant
    go (Builtin ann bi)         = Builtin ann bi
    go (TyInst ann fun arg)     = TyInst ann (go fun) arg
    go (Unwrap ann term)        = Unwrap ann (go term)
    go (IWrap ann pat arg term) = IWrap ann pat arg (go term)
    go (Error ann ty)           = Error ann ty

    goUnder var term = if var == varFor then term else go term

-- | The computing part of the CK machine. Rules are as follows:
--
-- > s ▷ {M A}      ↦ s , {_ A}        ▷ M
-- > s ▷ [M N]      ↦ s , [_ N]        ▷ M
-- > s ▷ wrap α A M ↦ s , (wrap α S _) ▷ M
-- > s ▷ unwrap M   ↦ s , (unwrap _)   ▷ M
-- > s ▷ abs α K M  ↦ s                ◁ abs α K M
-- > s ▷ lam x A M  ↦ s                ◁ lam x A M
-- > s ▷ con cn     ↦ s                ◁ con cn
-- > s ▷ error A    ↦ ◆
(|>)
    :: Evaluable uni
    => Context uni -> Term TyName Name uni () -> CkM uni (EvaluationResultDef uni)
stack |> TyInst _ fun ty        = FrameTyInstArg ty      : stack |> fun
stack |> Apply _ fun arg        = FrameApplyArg arg      : stack |> fun
stack |> IWrap ann pat arg term = FrameIWrap ann pat arg : stack |> term
stack |> Unwrap _ term          = FrameUnwrap            : stack |> term
stack |> tyAbs@TyAbs{}          = stack <| tyAbs
stack |> lamAbs@LamAbs{}        = stack <| lamAbs
stack |> bi@Builtin{}           = stack <| bi
stack |> constant@Constant{}    = stack <| constant
_     |> Error{}                = pure EvaluationFailure
_     |> var@Var{}              = throwCkMachineException OpenTermEvaluatedMachineError var

-- | The returning part of the CK machine. Rules are as follows:
--
-- > s , {_ A}           ◁ abs α K M  ↦ s         ▷ M
-- > s , [_ N]           ◁ V          ↦ s , [V _] ▷ N
-- > s , [(lam x A M) _] ◁ V          ↦ s         ▷ [V/x]M
-- > s , {_ A}           ◁ F          ↦ s         ◁ {F A}  -- Partially saturated constant.
-- > s , [F _]           ◁ V          ↦ s         ◁ [F V]  -- Partially saturated constant.
-- > s , [F _]           ◁ V          ↦ s         ◁ W      -- Fully saturated constant, [F V] ~> W.
-- > s , (wrap α S _)    ◁ V          ↦ s         ◁ wrap α S V
-- > s , (unwrap _)      ◁ wrap α A V ↦ s         ◁ V
(<|)
    :: Evaluable uni
    => Context uni -> Value TyName Name uni () -> CkM uni (EvaluationResultDef uni)
[]                             <| term    = pure $ EvaluationSuccess term
FrameTyInstArg ty      : stack <| fun     = instantiateEvaluate stack ty fun
FrameApplyArg arg      : stack <| fun     = FrameApplyFun fun : stack |> arg
FrameApplyFun fun      : stack <| arg     = applyEvaluate stack fun arg
FrameIWrap ann pat arg : stack <| value   = stack <| IWrap ann pat arg value
FrameUnwrap            : stack <| wrapped = case wrapped of
    IWrap _ _ _ term -> stack <| term
    term             -> throwCkMachineException NonWrapUnwrappedMachineError term

-- | Instantiate a term with a type and proceed.
-- In case of 'TyAbs' just ignore the type. Otherwise check if the term is an
-- iterated application of a 'BuiltinName' to a list of 'Value's and, if succesful,
-- apply the term to the type via 'TyInst'.
instantiateEvaluate
    :: Evaluable uni
    => Context uni
    -> Type TyName uni ()
    -> Term TyName Name uni ()
    -> CkM uni (EvaluationResultDef uni)
instantiateEvaluate stack _  (TyAbs _ _ _ body) = stack |> body
instantiateEvaluate stack ty fun
    | isJust $ termAsPrimIterApp fun = stack <| TyInst () fun ty
    | otherwise                      =
        throwCkMachineException NonPrimitiveInstantiationMachineError fun

-- | Apply a function to an argument and proceed.
-- If the function is not a 'LamAbs', then 'Apply' it to the argument and view this
-- as an iterated application of a 'BuiltinName' to a list of 'Value's.
-- If succesful, proceed with either this same term or with the result of the computation
-- depending on whether 'BuiltinName' is saturated or not.
applyEvaluate
    :: Evaluable uni
    => Context uni
    -> Value TyName Name uni ()
    -> Value TyName Name uni ()
    -> CkM uni (EvaluationResultDef uni)
applyEvaluate stack (LamAbs _ name _ body) arg = stack |> substituteDb name arg body
applyEvaluate stack fun                    arg =
    let term = Apply () fun arg in
        case termAsPrimIterApp term of
            Nothing                       ->
                throwCkMachineException NonPrimitiveApplicationMachineError term
            Just (IterApp headName spine) -> do
                constAppResult <- applyStagedBuiltinName headName spine
                case constAppResult of
                    ConstAppSuccess term' -> stack |> term'
                    ConstAppFailure       -> pure EvaluationFailure
                    ConstAppStuck         -> stack <| term
                    ConstAppError err     ->
                        throwCkMachineException (ConstAppMachineError err) term

evaluateInCkM :: forall uni a. EvaluateConstApp uni (CkM uni) a -> CkM uni (ConstAppResult uni a)
evaluateInCkM =
    runEvaluateConstApp $ Evaluator $ \emb meansExt term -> do
        let extend means = embedNameMeanings emb means <> meansExt
        withReader extend $ [] |> term

-- | Apply a 'StagedBuiltinName' to a list of 'Value's.
applyStagedBuiltinName
    :: Evaluable uni
    => StagedBuiltinName -> [Value TyName Name uni ()] -> CkM uni (ConstAppResultDef uni)
applyStagedBuiltinName (DynamicStagedBuiltinName name) args = do
    NameMeaning sch x <- lookupDynamicBuiltinName name
    evaluateInCkM $ applyTypeSchemed sch x args
applyStagedBuiltinName (StaticStagedBuiltinName  name) args =
    evaluateInCkM $ applyBuiltinName name args

applyEvaluateCkBuiltinName
    :: Evaluable uni => BuiltinName -> [Value TyName Name uni ()] -> ConstAppResultDef uni
applyEvaluateCkBuiltinName name = runIdentity . runApplyBuiltinName evaluatorCk name

evaluatorCk :: Evaluator Term uni Identity
evaluatorCk = Evaluator $ \_ -> Identity .* evaluateCk

readKnownCk :: KnownType a uni => Term TyName Name uni () -> EvaluationResult (Either Text a)
readKnownCk = runIdentity . runReflectT . readKnown evaluatorCk

-- | Evaluate a term using the CK machine. May throw a 'CkMachineException'.
-- This differs from the spec version: we do not have the following rule:
--
-- > s , {_ A} ◁ F ↦ s ◁ W  -- Fully saturated constant, {F A} ~> W.
--
-- The reason for that is that the operational semantics of constant applications is
-- unaffected by types as it supports full type erasure, hence @{F A}@ can never compute
-- if @F@ does not compute, so we simply do not introduce a rule that can't possibly fire.
evaluateCk
    :: Evaluable uni
    => NameMeanings uni -> Term TyName Name uni () -> EvaluationResultDef uni
evaluateCk means term = runCkM means $ [] |> term

-- | Run a program using the CK machine. May throw a 'CkMachineException'.
-- Calls 'evaluateCk' under the hood, so the same caveats apply.
runCk
    :: Evaluable uni
    => NameMeanings uni -> Program TyName Name uni () -> EvaluationResultDef uni
runCk means (Program _ _ term) = evaluateCk means term
