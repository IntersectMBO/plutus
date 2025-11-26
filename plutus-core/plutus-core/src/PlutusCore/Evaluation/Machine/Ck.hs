-- editorconfig-checker-disable-file
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

-- | The CK machine.
module PlutusCore.Evaluation.Machine.Ck
  ( EvaluationResult (..)
  , CkEvaluationException
  , CkM
  , CkValue
  , runCk
  , splitStructuralOperational
  , unsafeSplitStructuralOperational
  , evaluateCk
  , evaluateCkNoEmit
  , readKnownCk
  ) where

import PlutusPrelude

import PlutusCore.Builtin
import PlutusCore.Core
import PlutusCore.Evaluation.Machine.ExMemoryUsage
import PlutusCore.Evaluation.Machine.Exception
import PlutusCore.Evaluation.Result
import PlutusCore.Name.Unique
import PlutusCore.Pretty
import PlutusCore.Subst

import Control.Lens ((^?))
import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.ST
import Data.Bifunctor
import Data.DList (DList)
import Data.DList qualified as DList
import Data.List.Extras (wix)
import Data.STRef
import Data.Text (Text)
import Data.Vector qualified as Vector
import Data.Word
import Prettyprinter (vcat)
import Universe

infix 4 |>, <|

-- See Note [Show instance for BuiltinRuntime] in the CEK machine.
instance Show (BuiltinRuntime (CkValue uni fun)) where
  show _ = "<builtin_runtime>"

data CkValue uni fun
  = VCon (Some (ValueOf uni))
  | VTyAbs TyName (Kind ()) (Term TyName Name uni fun ())
  | VLamAbs Name (Type TyName uni ()) (Term TyName Name uni fun ())
  | VIWrap (Type TyName uni ()) (Type TyName uni ()) (CkValue uni fun)
  | VBuiltin (Term TyName Name uni fun ()) (BuiltinRuntime (CkValue uni fun))
  | VConstr (Type TyName uni ()) Word64 [CkValue uni fun]

deriving stock instance
  (GShow uni, Everywhere uni Show, Show fun, Closed uni)
  => Show (CkValue uni fun)

ckValueToTerm :: CkValue uni fun -> Term TyName Name uni fun ()
ckValueToTerm = \case
  VCon val -> Constant () val
  VTyAbs tn k body -> TyAbs () tn k body
  VLamAbs name ty body -> LamAbs () name ty body
  VIWrap ty1 ty2 val -> IWrap () ty1 ty2 $ ckValueToTerm val
  VBuiltin term _ -> term
  VConstr ty i es -> Constr () ty i (fmap ckValueToTerm es)

data CkEnv uni fun s = CkEnv
  { ckEnvRuntime :: BuiltinsRuntime fun (CkValue uni fun)
  , ckCaserBuiltin :: CaserBuiltin uni
  , -- 'Nothing' means no logging. 'DList' is due to the fact that we need efficient append
    -- as we store logs as "latest go last".
    ckEnvMayEmitRef :: Maybe (STRef s (DList Text))
  }

instance (PrettyUni uni, Pretty fun) => PrettyBy PrettyConfigPlc (CkValue uni fun) where
  prettyBy cfg = prettyBy cfg . ckValueToTerm

data CkUserError
  = -- | 'Case' over a value of a built-in type failed.
    CkCaseBuiltinError Text
  | CkEvaluationFailure -- Error has been called or a builtin application has failed
  deriving stock (Show, Eq, Generic)
  deriving anyclass (NFData)

-- | The CK machine-specific 'EvaluationException'.
type CkEvaluationException uni fun =
  EvaluationException (MachineError fun) CkUserError (Term TyName Name uni fun ())

type CkM uni fun s =
  ReaderT
    (CkEnv uni fun s)
    ( ExceptT
        (CkEvaluationException uni fun)
        (ST s)
    )

instance Pretty CkUserError where
  pretty (CkCaseBuiltinError err) =
    vcat
      [ "'case' over a value of a built-in type failed with"
      , pretty err
      ]
  pretty CkEvaluationFailure = "The provided Plutus code called 'error'."

instance BuiltinErrorToEvaluationError (MachineError fun) CkUserError where
  builtinErrorToEvaluationError (BuiltinUnliftingEvaluationError err) =
    bimap UnliftingMachineError (const CkEvaluationFailure) (unUnliftingEvaluationError err)
  builtinErrorToEvaluationError BuiltinEvaluationFailure =
    OperationalError CkEvaluationFailure
  {-# INLINE builtinErrorToEvaluationError #-}

-- The 'DList' is just be consistent with the CEK machine (see Note [DList-based emitting]).
emitCkM :: DList Text -> CkM uni fun s ()
emitCkM logs = do
  mayLogsRef <- asks ckEnvMayEmitRef
  case mayLogsRef of
    Nothing -> pure ()
    Just logsRef -> lift . lift $ modifySTRef logsRef (`DList.append` logs)

type instance UniOf (CkValue uni fun) = uni

instance HasConstant (CkValue uni fun) where
  asConstant (VCon val) = pure val
  asConstant _ = throwError notAConstant

  fromConstant = VCon

data Frame uni fun
  = -- | @[V _]@
    FrameAwaitArg (CkValue uni fun)
  | -- | @[_ N]@
    FrameAwaitFunTerm (Term TyName Name uni fun ())
  | -- | @[_ V]@
    FrameAwaitFunValue (CkValue uni fun)
  | -- | @{_ A}@
    FrameTyInstArg (Type TyName uni ())
  | -- | @(unwrap _)@
    FrameUnwrap
  | -- | @(iwrap A B _)@
    FrameIWrap (Type TyName uni ()) (Type TyName uni ())
  | FrameConstr (Type TyName uni ()) Word64 [Term TyName Name uni fun ()] [CkValue uni fun]
  | FrameCase [Term TyName Name uni fun ()]

deriving stock instance
  (GShow uni, Closed uni, uni `Everywhere` Show, Show fun)
  => Show (Frame uni fun)

type Context uni fun = [Frame uni fun]

-- See Note [ExMemoryUsage instances for non-constants].
instance ExMemoryUsage (CkValue uni fun) where
  memoryUsage = error "Internal error: 'memoryUsage' for 'CkValue' is not supposed to be forced"

runCkM
  :: BuiltinsRuntime fun (CkValue uni fun)
  -> CaserBuiltin uni
  -> Bool
  -> (forall s. CkM uni fun s a)
  -> (Either (CkEvaluationException uni fun) a, [Text])
runCkM runtime caser emitting a = runST $ do
  mayLogsRef <- if emitting then Just <$> newSTRef DList.empty else pure Nothing
  errOrRes <- runExceptT . runReaderT a $ CkEnv runtime caser mayLogsRef
  logs <- case mayLogsRef of
    Nothing -> pure []
    Just logsRef -> DList.toList <$> readSTRef logsRef
  pure (errOrRes, logs)

-- FIXME: make sure that the specification is up to date and that this matches.
-- Tracked by https://github.com/IntersectMBO/plutus-private/issues/1552.
{-| The computing part of the CK machine. Rules are as follows:

> s ▷ {M A}      ↦ s , {_ A}        ▷ M
> s ▷ [M N]      ↦ s , [_ N]        ▷ M
> s ▷ wrap α A M ↦ s , (wrap α S _) ▷ M
> s ▷ unwrap M   ↦ s , (unwrap _)   ▷ M
> s ▷ abs α K M  ↦ s ◁ abs α K M
> s ▷ lam x A M  ↦ s ◁ lam x A M
> s ▷ builtin bn ↦ s ◁ builtin (Builtin () bn) (runtimeOf bn)
> s ▷ con cn     ↦ s ◁ con cn
> s ▻ constr I T0 .. Tn ↦ s , (constr I _ T1 Tn) ▻ T0
> s ▻ case S C0 ... Cn ↦ s , (case _ C0 ... Cn) ▻ S
> s ▷ error A    ↦ ◆ -}
(|>)
  :: Context uni fun -> Term TyName Name uni fun () -> CkM uni fun s (Term TyName Name uni fun ())
stack |> TyInst _ fun ty = FrameTyInstArg ty : stack |> fun
stack |> Apply _ fun arg = FrameAwaitFunTerm arg : stack |> fun
stack |> IWrap _ pat arg term = FrameIWrap pat arg : stack |> term
stack |> Unwrap _ term = FrameUnwrap : stack |> term
stack |> TyAbs _ tn k term = stack <| VTyAbs tn k term
stack |> LamAbs _ name ty body = stack <| VLamAbs name ty body
stack |> Builtin _ bn = do
  runtime <- lookupBuiltin bn . ckEnvRuntime <$> ask
  stack <| VBuiltin (Builtin () bn) runtime
stack |> Constant _ val = stack <| VCon val
stack |> Constr _ ty i es = case es of
  [] -> stack <| VConstr ty i []
  t : ts -> FrameConstr ty i ts [] : stack |> t
stack |> Case _ _ arg cs = FrameCase cs : stack |> arg
_ |> err@Error {} =
  throwErrorWithCause (OperationalError CkEvaluationFailure) $ void err
_ |> var@Var {} =
  throwErrorWithCause (StructuralError OpenTermEvaluatedMachineError) var

-- FIXME: make sure that the specification is up to date and that this matches.
-- Tracked by https://github.com/IntersectMBO/plutus-private/issues/1552.
{-| The returning part of the CK machine. Rules are as follows:

> s , {_ A}           ◁ abs α K M  ↦ s         ▷ {A/α}M
> s , [_ N]           ◁ V          ↦ s , [V _] ▷ N
> s , [_ V1 ... Vm]   ◁ (lam x A M) ↦ s , [_ V2 ... Vm] ▷ [V1/x]M
> s , [(lam x A M) _] ◁ V          ↦ s         ▷ [V/x]M
> s , {_ A}           ◁ F          ↦ s ◁ {F A}  -- Partially instantiated builtin application.
> s , [F _]           ◁ V          ↦ s ◁ [F V]  -- Partially saturated builtin application.
> s , [F _]           ◁ V          ↦ s ◁ W      -- Fully saturated builtin application, [F V] ~> W.
> s , (wrap α S _)    ◁ V          ↦ s ◁ wrap α S V
> s , (unwrap _)      ◁ wrap α A V ↦ s ◁ V
> s , (constr I V0 ... Vj-1 _ Tj+1 ... Tn) ◅ Vj ↦ s , (constr i V0 ... Vj _ Tj+2... Tn) ▻ Tj+1
> s , (case _ C0 ... CN) ◅ (constr i V1 .. Vm) ↦ s , [_ V1 ... Vm] ▻ Ci -}
(<|)
  :: Context uni fun -> CkValue uni fun -> CkM uni fun s (Term TyName Name uni fun ())
[] <| val = pure $ ckValueToTerm val
FrameTyInstArg ty : stack <| fun = instantiateEvaluate stack ty fun
FrameAwaitFunTerm arg : stack <| fun = FrameAwaitArg fun : stack |> arg
FrameAwaitArg fun : stack <| arg = applyEvaluate stack fun arg
FrameAwaitFunValue arg : stack <| fun = applyEvaluate stack fun arg
FrameIWrap pat arg : stack <| value = stack <| VIWrap pat arg value
FrameUnwrap : stack <| wrapped = case wrapped of
  VIWrap _ _ term -> stack <| term
  _ ->
    throwErrorWithCause (StructuralError NonWrapUnwrappedMachineError) $ ckValueToTerm wrapped
FrameConstr ty i todo done : stack <| e =
  let done' = e : done
   in case todo of
        t : ts -> FrameConstr ty i ts done' : stack |> t
        [] -> stack <| VConstr ty i (reverse done')
FrameCase cs : stack <| e = case e of
  VConstr _ i args -> case cs ^? wix i of
    Just t -> go (reverse args) stack |> t
      where
        go [] s = s
        go (arg : rest) s = go rest (FrameAwaitFunValue arg : s)
    Nothing ->
      throwErrorWithCause (StructuralError $ MissingCaseBranchMachineError i) $ ckValueToTerm e
  VCon val -> do
    caser <- asks ckCaserBuiltin
    case unCaserBuiltin caser val $ Vector.fromList cs of
      HeadError err ->
        throwErrorWithCause (OperationalError $ CkCaseBuiltinError err) $ ckValueToTerm e
      HeadOnly fX -> stack |> fX
      HeadSpine f xs -> transferConstantSpine xs stack |> f
  _ -> throwErrorWithCause (StructuralError NonConstrScrutinizedMachineError) $ ckValueToTerm e

transferConstantSpine :: Spine (Some (ValueOf uni)) -> Context uni fun -> Context uni fun
transferConstantSpine args ctx = foldr ((:) . FrameAwaitFunValue . VCon) ctx args

{-| Take a possibly partial builtin application and

- either create a 'CkValue' by evaluating the application if it's saturated (emitting logs, if
   any, along the way), potentially failing evaluation
- or create a partial builtin application otherwise

and proceed with the returning phase of the CK machine. -}
evalBuiltinApp
  :: Context uni fun
  -> Term TyName Name uni fun ()
  -> BuiltinRuntime (CkValue uni fun)
  -> CkM uni fun s (Term TyName Name uni fun ())
evalBuiltinApp stack term runtime = case runtime of
  BuiltinCostedResult _ getFXs -> case getFXs of
    BuiltinSuccess y -> stack <| y
    BuiltinSuccessWithLogs logs y -> emitCkM logs *> (stack <| y)
    BuiltinFailure logs err -> emitCkM logs *> throwBuiltinErrorWithCause term err
  _ -> stack <| VBuiltin term runtime

{-| Instantiate a term with a type and proceed.
In case of 'TyAbs' just ignore the type. Otherwise check if the term is builtin application
expecting a type argument, in which case either calculate the builtin application or stick a
'TyInst' on top of its 'Term' representation depending on whether the application is saturated or
not. In any other case, fail. -}
instantiateEvaluate
  :: Context uni fun
  -> Type TyName uni ()
  -> CkValue uni fun
  -> CkM uni fun s (Term TyName Name uni fun ())
instantiateEvaluate stack ty (VTyAbs tn _k body) =
  -- No kind check - too expensive at run time.
  stack |> termSubstClosedType tn ty body
instantiateEvaluate stack ty (VBuiltin term runtime) = do
  let term' = TyInst () term ty
  case runtime of
    -- We allow a type argument to appear last in the type of a built-in function,
    -- otherwise we could just assemble a 'VBuiltin' without trying to evaluate the
    -- application.
    BuiltinExpectForce runtime' -> evalBuiltinApp stack term' runtime'
    _ -> throwErrorWithCause (StructuralError BuiltinTermArgumentExpectedMachineError) term'
instantiateEvaluate _ _ val =
  throwErrorWithCause (StructuralError NonPolymorphicInstantiationMachineError) $ ckValueToTerm val

{-| Apply a function to an argument and proceed.
If the function is a lambda, then perform substitution and proceed.
If the function is a builtin application then check that it's expecting a term argument,
and either calculate the builtin application or stick a 'Apply' on top of its 'Term'
representation depending on whether the application is saturated or not. -}
applyEvaluate
  :: Context uni fun
  -> CkValue uni fun
  -> CkValue uni fun
  -> CkM uni fun s (Term TyName Name uni fun ())
applyEvaluate stack (VLamAbs name _ body) arg =
  stack |> termSubstClosedTerm name (ckValueToTerm arg) body
applyEvaluate stack (VBuiltin term runtime) arg = do
  let argTerm = ckValueToTerm arg
      term' = Apply () term argTerm
  case runtime of
    -- It's only possible to apply a builtin application if the builtin expects a term
    -- argument next.
    BuiltinExpectArgument f -> do
      evalBuiltinApp stack term' $ f arg
    _ ->
      throwErrorWithCause (StructuralError UnexpectedBuiltinTermArgumentMachineError) term'
applyEvaluate _ val _ =
  throwErrorWithCause (StructuralError NonFunctionalApplicationMachineError) $ ckValueToTerm val

runCk
  :: BuiltinsRuntime fun (CkValue uni fun)
  -> CaserBuiltin uni
  -> Bool
  -> Term TyName Name uni fun ()
  -> (Either (CkEvaluationException uni fun) (Term TyName Name uni fun ()), [Text])
runCk runtime caser emitting term = runCkM runtime caser emitting $ [] |> term

-- | Evaluate a term using the CK machine with logging enabled.
evaluateCk
  :: BuiltinsRuntime fun (CkValue uni fun)
  -> CaserBuiltin uni
  -> Term TyName Name uni fun ()
  -> (Either (CkEvaluationException uni fun) (Term TyName Name uni fun ()), [Text])
evaluateCk runtime caser = runCk runtime caser True

-- | Evaluate a term using the CK machine with logging disabled.
evaluateCkNoEmit
  :: BuiltinsRuntime fun (CkValue uni fun)
  -> CaserBuiltin uni
  -> Term TyName Name uni fun ()
  -> Either (CkEvaluationException uni fun) (Term TyName Name uni fun ())
evaluateCkNoEmit runtime caser = fst . runCk runtime caser False

-- | Unlift a value using the CK machine.
readKnownCk
  :: ReadKnown (Term TyName Name uni fun ()) a
  => BuiltinsRuntime fun (CkValue uni fun)
  -> CaserBuiltin uni
  -> Term TyName Name uni fun ()
  -> Either (CkEvaluationException uni fun) a
readKnownCk runtime caser = evaluateCkNoEmit runtime caser >=> readKnownSelf
