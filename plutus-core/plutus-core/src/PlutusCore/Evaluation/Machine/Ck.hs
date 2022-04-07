-- | The CK machine.

{-# LANGUAGE DeriveAnyClass            #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE LambdaCase                #-}
{-# LANGUAGE MultiParamTypeClasses     #-}
{-# LANGUAGE OverloadedStrings         #-}
{-# LANGUAGE RankNTypes                #-}
{-# LANGUAGE TypeApplications          #-}
{-# LANGUAGE TypeFamilies              #-}
{-# LANGUAGE TypeOperators             #-}
{-# LANGUAGE UndecidableInstances      #-}

module PlutusCore.Evaluation.Machine.Ck
    ( EvaluationResult (..)
    , CkEvaluationException
    , CkM
    , CkValue
    , extractEvaluationResult
    , runCk
    , evaluateCk
    , evaluateCkNoEmit
    , unsafeEvaluateCk
    , unsafeEvaluateCkNoEmit
    , readKnownCk
    ) where

import PlutusPrelude

import PlutusCore.Builtin
import PlutusCore.Core
import PlutusCore.Evaluation.Machine.Exception
import PlutusCore.Evaluation.Result
import PlutusCore.Name
import PlutusCore.Pretty (PrettyConfigPlc, PrettyConst)

import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.ST
import Data.Array
import Data.DList (DList)
import Data.DList qualified as DList
import Data.STRef
import Data.Text (Text)
import Universe

infix 4 |>, <|

-- See Note [Show instance for BuiltinRuntime] in the CEK machine.
instance Show (BuiltinRuntime (CkValue uni fun)) where
    show _ = "<builtin_runtime>"

data CkValue uni fun =
    VCon (Some (ValueOf uni))
  | VTyAbs TyName (Kind ()) (Term TyName Name uni fun ())
  | VLamAbs Name (Type TyName uni ()) (Term TyName Name uni fun ())
  | VIWrap (Type TyName uni ()) (Type TyName uni ()) (CkValue uni fun)
  | VBuiltin (Term TyName Name uni fun ()) (BuiltinRuntime (CkValue uni fun))
    deriving stock (Show)

-- | Take pieces of a possibly partial builtin application and either create a 'CkValue' using
-- 'makeKnown' or a partial builtin application depending on whether the built-in function is
-- fully saturated or not.
evalBuiltinApp
    :: Term TyName Name uni fun ()
    -> BuiltinRuntime (CkValue uni fun)
    -> CkM uni fun s (CkValue uni fun)
evalBuiltinApp term runtime@(BuiltinRuntime sch getX _) = case sch of
    RuntimeSchemeResult -> do
        let (errOrRes, logs) = runEmitter $ runExceptT getX
        emitCkM logs
        case errOrRes of
            Left err  -> throwKnownTypeErrorWithCause $ term <$ err
            Right res -> pure res
    _ -> pure $ VBuiltin term runtime

ckValueToTerm :: CkValue uni fun -> Term TyName Name uni fun ()
ckValueToTerm = \case
    VCon val             -> Constant () val
    VTyAbs  tn k body    -> TyAbs  () tn k body
    VLamAbs name ty body -> LamAbs () name ty body
    VIWrap  ty1 ty2 val  -> IWrap  () ty1 ty2 $ ckValueToTerm val
    VBuiltin term _      -> term

data CkEnv uni fun s = CkEnv
    { ckEnvRuntime    :: BuiltinsRuntime fun (CkValue uni fun)
    -- 'Nothing' means no logging. 'DList' is due to the fact that we need efficient append
    -- as we store logs as "latest go last".
    , ckEnvMayEmitRef :: Maybe (STRef s (DList Text))
    }

instance (Closed uni, GShow uni, uni `Everywhere` PrettyConst, Pretty fun) =>
            PrettyBy PrettyConfigPlc (CkValue uni fun) where
    prettyBy cfg = prettyBy cfg . ckValueToTerm

data CkUserError =
    CkEvaluationFailure -- Error has been called or a builtin application has failed
    deriving stock (Show, Eq, Generic)
    deriving anyclass (NFData)

-- | The CK machine-specific 'EvaluationException'.
type CkEvaluationException uni fun =
    EvaluationException CkUserError (MachineError fun) (Term TyName Name uni fun ())

type CkM uni fun s =
    ReaderT (CkEnv uni fun s)
        (ExceptT (CkEvaluationException uni fun)
            (ST s))

instance AsEvaluationFailure CkUserError where
    _EvaluationFailure = _EvaluationFailureVia CkEvaluationFailure

instance Pretty CkUserError where
    pretty CkEvaluationFailure = "The provided Plutus code called 'error'."

-- The 'DList' is just be consistent with the CEK machine (see Note [DList-based emitting]).
emitCkM :: DList Text -> CkM uni fun s ()
emitCkM logs = do
    mayLogsRef <- asks ckEnvMayEmitRef
    case mayLogsRef of
        Nothing      -> pure ()
        Just logsRef -> lift . lift $ modifySTRef logsRef (`DList.append` logs)

type instance UniOf (CkValue uni fun) = uni

instance HasConstant (CkValue uni fun) where
    asConstant _        (VCon val) = pure val
    asConstant mayCause _          = throwNotAConstant mayCause

    fromConstant = VCon

data Frame uni fun
    = FrameApplyFun (CkValue uni fun)                       -- ^ @[V _]@
    | FrameApplyArg (Term TyName Name uni fun ())           -- ^ @[_ N]@
    | FrameTyInstArg (Type TyName uni ())                   -- ^ @{_ A}@
    | FrameUnwrap                                           -- ^ @(unwrap _)@
    | FrameIWrap (Type TyName uni ()) (Type TyName uni ())  -- ^ @(iwrap A B _)@

type Context uni fun = [Frame uni fun]

runCkM
    :: BuiltinsRuntime fun (CkValue uni fun)
    -> Bool
    -> (forall s. CkM uni fun s a)
    -> (Either (CkEvaluationException uni fun) a, [Text])
runCkM runtime emitting a = runST $ do
    mayLogsRef <- if emitting then Just <$> newSTRef DList.empty else pure Nothing
    errOrRes <- runExceptT . runReaderT a $ CkEnv runtime mayLogsRef
    logs <- case mayLogsRef of
        Nothing      -> pure []
        Just logsRef -> DList.toList <$> readSTRef logsRef
    pure (errOrRes, logs)

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
-- > s ▷ builtin bn ↦ s ◁ builtin (Builtin () bn) (runtimeOf bn)
-- > s ▷ con cn     ↦ s ◁ con cn
-- > s ▷ error A    ↦ ◆
(|>)
    :: Ix fun
    => Context uni fun -> Term TyName Name uni fun () -> CkM uni fun s (Term TyName Name uni fun ())
stack |> TyInst  _ fun ty        = FrameTyInstArg ty  : stack |> fun
stack |> Apply   _ fun arg       = FrameApplyArg arg  : stack |> fun
stack |> IWrap   _ pat arg term  = FrameIWrap pat arg : stack |> term
stack |> Unwrap  _ term          = FrameUnwrap        : stack |> term
stack |> TyAbs   _ tn k term     = stack <| VTyAbs tn k term
stack |> LamAbs  _ name ty body  = stack <| VLamAbs name ty body
stack |> Builtin _ bn            = do
    runtime <- asksM $ lookupBuiltin bn . ckEnvRuntime
    stack <| VBuiltin (Builtin () bn) runtime
stack |> Constant _ val          = stack <| VCon val
_     |> Error{}                 =
    throwingWithCause _EvaluationError (UserEvaluationError CkEvaluationFailure) Nothing
_     |> var@Var{}               =
    throwingWithCause _MachineError OpenTermEvaluatedMachineError $ Just var


-- FIXME: make sure that the specification is up to date and that this matches.
-- | The returning part of the CK machine. Rules are as follows:
--
-- > s , {_ A}           ◁ abs α K M  ↦ s         ▷ {A/α}M
-- > s , [_ N]           ◁ V          ↦ s , [V _] ▷ N
-- > s , [(lam x A M) _] ◁ V          ↦ s         ▷ [V/x]M
-- > s , {_ A}           ◁ F          ↦ s ◁ {F A}  -- Partially instantiated builtin application.
-- > s , [F _]           ◁ V          ↦ s ◁ [F V]  -- Partially saturated builtin application.
-- > s , [F _]           ◁ V          ↦ s ◁ W      -- Fully saturated builtin application, [F V] ~> W.
-- > s , (wrap α S _)    ◁ V          ↦ s ◁ wrap α S V
-- > s , (unwrap _)      ◁ wrap α A V ↦ s ◁ V
(<|)
    :: Ix fun
    => Context uni fun -> CkValue uni fun -> CkM uni fun s (Term TyName Name uni fun ())
[]                         <| val     = pure $ ckValueToTerm val
FrameTyInstArg ty  : stack <| fun     = instantiateEvaluate stack ty fun
FrameApplyArg arg  : stack <| fun     = FrameApplyFun fun : stack |> arg
FrameApplyFun fun  : stack <| arg     = applyEvaluate stack fun arg
FrameIWrap pat arg : stack <| value   = stack <| VIWrap pat arg value
FrameUnwrap        : stack <| wrapped = case wrapped of
    VIWrap _ _ term -> stack <| term
    _               ->
        throwingWithCause _MachineError NonWrapUnwrappedMachineError $ Just $ ckValueToTerm wrapped

-- | Instantiate a term with a type and proceed.
-- In case of 'TyAbs' just ignore the type. Otherwise check if the term is builtin application
-- expecting a type argument, in which case either calculate the builtin application or stick a
-- 'TyInst' on top of its 'Term' representation depending on whether the application is saturated or
-- not. In any other case, fail.
instantiateEvaluate
    :: Ix fun
    => Context uni fun
    -> Type TyName uni ()
    -> CkValue uni fun
    -> CkM uni fun s (Term TyName Name uni fun ())
instantiateEvaluate stack ty (VTyAbs tn _k body) = stack |> substTyInTerm tn ty body -- No kind check - too expensive at run time.
instantiateEvaluate stack ty (VBuiltin term (BuiltinRuntime sch f exF)) = do
    let term' = TyInst () term ty
    case sch of
        -- We allow a type argument to appear last in the type of a built-in function,
        -- otherwise we could just assemble a 'VBuiltin' without trying to evaluate the
        -- application.
        RuntimeSchemeAll schK -> do
            let runtime' = BuiltinRuntime schK f exF
            res <- evalBuiltinApp term' runtime'
            stack <| res
        _ -> throwingWithCause _MachineError BuiltinTermArgumentExpectedMachineError (Just term')
instantiateEvaluate _ _ val =
    throwingWithCause _MachineError NonPolymorphicInstantiationMachineError $ Just $ ckValueToTerm val

-- | Apply a function to an argument and proceed.
-- If the function is a lambda, then perform substitution and proceed.
-- If the function is a builtin application then check that it's expecting a term argument,
-- and either calculate the builtin application or stick a 'Apply' on top of its 'Term'
-- representation depending on whether the application is saturated or not.
applyEvaluate
    :: Ix fun
    => Context uni fun
    -> CkValue uni fun
    -> CkValue uni fun
    -> CkM uni fun s (Term TyName Name uni fun ())
applyEvaluate stack (VLamAbs name _ body) arg = stack |> substituteDb name (ckValueToTerm arg) body
applyEvaluate stack (VBuiltin term (BuiltinRuntime sch f exF)) arg = do
    let argTerm = ckValueToTerm arg
        term' = Apply () term argTerm
    case sch of
        -- It's only possible to apply a builtin application if the builtin expects a term
        -- argument next.
        RuntimeSchemeArrow schB -> case f arg of
            Left err -> throwKnownTypeErrorWithCause $ argTerm <$ err
            Right y  -> do
                -- The CK machine does not support costing, so we just apply the costing function
                -- to 'mempty'.
                let runtime' = BuiltinRuntime schB y (exF mempty)
                res <- evalBuiltinApp term' runtime'
                stack <| res
        _ ->
            throwingWithCause _MachineError UnexpectedBuiltinTermArgumentMachineError (Just term')
applyEvaluate _ val _ =
    throwingWithCause _MachineError NonFunctionalApplicationMachineError $ Just $ ckValueToTerm val

runCk
    :: Ix fun
    => BuiltinsRuntime fun (CkValue uni fun)
    -> Bool
    -> Term TyName Name uni fun ()
    -> (Either (CkEvaluationException uni fun) (Term TyName Name uni fun ()), [Text])
runCk runtime emitting term = runCkM runtime emitting $ [] |> term

-- | Evaluate a term using the CK machine with logging enabled.
evaluateCk
    :: Ix fun
    => BuiltinsRuntime fun (CkValue uni fun)
    -> Term TyName Name uni fun ()
    -> (Either (CkEvaluationException uni fun) (Term TyName Name uni fun ()), [Text])
evaluateCk runtime = runCk runtime True

-- | Evaluate a term using the CK machine with logging disabled.
evaluateCkNoEmit
    :: Ix fun
    => BuiltinsRuntime fun (CkValue uni fun)
    -> Term TyName Name uni fun ()
    -> Either (CkEvaluationException uni fun) (Term TyName Name uni fun ())
evaluateCkNoEmit runtime = fst . runCk runtime False

-- | Evaluate a term using the CK machine with logging enabled. May throw a 'CkEvaluationException'.
unsafeEvaluateCk
    :: ( GShow uni, Closed uni
       , Typeable uni, Typeable fun, uni `Everywhere` PrettyConst
       , Pretty fun, Ix fun
       )
    => BuiltinsRuntime fun (CkValue uni fun)
    -> Term TyName Name uni fun ()
    -> (EvaluationResult (Term TyName Name uni fun ()), [Text])
unsafeEvaluateCk runtime = first unsafeExtractEvaluationResult . evaluateCk runtime

-- | Evaluate a term using the CK machine with logging disabled. May throw a 'CkEvaluationException'.
unsafeEvaluateCkNoEmit
    :: ( GShow uni, Closed uni
       , Typeable uni, Typeable fun, uni `Everywhere` PrettyConst
       , Pretty fun, Ix fun
       )
    => BuiltinsRuntime fun (CkValue uni fun)
    -> Term TyName Name uni fun ()
    -> EvaluationResult (Term TyName Name uni fun ())
unsafeEvaluateCkNoEmit runtime = unsafeExtractEvaluationResult . evaluateCkNoEmit runtime

-- | Unlift a value using the CK machine.
readKnownCk
    :: (Ix fun, ReadKnown (Term TyName Name uni fun ()) a)
    => BuiltinsRuntime fun (CkValue uni fun)
    -> Term TyName Name uni fun ()
    -> Either (CkEvaluationException uni fun) a
readKnownCk runtime = evaluateCkNoEmit runtime >=> readKnownSelf
