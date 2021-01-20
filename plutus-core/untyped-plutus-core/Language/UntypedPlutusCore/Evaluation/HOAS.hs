{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE TypeFamilies          #-}

module Language.UntypedPlutusCore.Evaluation.HOAS where

import           Language.UntypedPlutusCore.Core

import           Language.PlutusCore.Constant
import           Language.PlutusCore.Evaluation.Machine.Exception
import           Language.PlutusCore.Evaluation.Result
import           Language.PlutusCore.Name
import           Language.PlutusCore.Pretty
import           Language.PlutusCore.Universe

import           Control.Exception
import           Control.Lens.TH
import           Control.Monad.Except
import           Data.Array
import           Data.Bifunctor
import           Data.Proxy
import           Data.Typeable

data HTerm m name uni fun ann
    = HConstant ann (Some (ValueOf uni))
    | HBuiltin ann fun
    | HVar ann name
    | HLamAbs ann name (HTerm m name uni fun ann -> m (HTerm m name uni fun ann))
    | HApply ann (HTerm m name uni fun ann) (HTerm m name uni fun ann)
    | HDelay ann (m (HTerm m name uni fun ann))
    | HForce ann (HTerm m name uni fun ann)
    | HError ann

type instance UniOf (HTerm m name uni fun ann) = uni

instance AsConstant (HTerm m name uni fun ann) where
    asConstant (HConstant _ val) = Just val
    asConstant _                 = Nothing

instance FromConstant (HTerm m name uni fun ()) where
    fromConstant = HConstant ()

data FreeVariableError name ann = FreeVariableError ann name
    deriving (Show, Eq)

data UserHoasError
    = HoasEvaluationFailure
    deriving (Show, Eq)

data InternalHoasError
    = UnexpectedVariableHoasError
    | UnliftingHoasError UnliftingError
    | ArityHoasError
    | TypeHoasError
    deriving (Show, Eq)

instance PrettyBy PrettyConfigPlc UserHoasError where
    prettyBy _ HoasEvaluationFailure = "EvaluationFailure"

instance PrettyBy PrettyConfigPlc InternalHoasError where
    prettyBy _ = pretty . show

type HoasException = EvaluationException UserHoasError InternalHoasError

instance AsEvaluationFailure UserHoasError where
    _EvaluationFailure = _EvaluationFailureVia HoasEvaluationFailure

data BuiltinApp unique name uni fun ann = BuiltinApp
    { _builtinAppTerm    :: EvalM unique name uni fun ann (Term name uni fun ann)
    , _builtinAppRuntime :: BuiltinRuntime (Value unique name uni fun ann)
    }

type Value unique name uni fun ann =
    HTerm (EvalM unique name uni fun ann) name uni (BuiltinApp unique name uni fun ann) ann

newtype EvalM unique name uni fun ann a = EvalM
    { unEvalM :: Either (HoasException (Value unique name uni fun ann)) a
    } deriving newtype
        ( Functor, Applicative, Monad
        , MonadError (HoasException (Value unique name uni fun ann))
        )

makeClassyPrisms ''UserHoasError
makeClassyPrisms ''InternalHoasError

instance AsInternalHoasError internal => AsInternalHoasError (EvaluationError user internal) where
    _InternalHoasError = _InternalEvaluationError . _InternalHoasError

instance AsUnliftingError InternalHoasError where
    _UnliftingError = _UnliftingHoasError

fromHTerm :: Monad m => HTerm m name uni fun ann -> m (Term name uni fun ann)
fromHTerm (HConstant ann val)     = pure $ Constant ann val
fromHTerm (HBuiltin ann fun)      = pure $ Builtin ann fun
fromHTerm (HVar ann name)         = pure $ Var ann name
-- Here we don't recover the original annotation and instead use the one that the whole lambda
-- is annotated with. We could probably handle annotations better, but we don't care for now.
fromHTerm (HLamAbs ann name body) = LamAbs ann name <$> (body (HVar ann name) >>= fromHTerm)
fromHTerm (HApply ann fun arg)    = Apply ann <$> fromHTerm fun <*> fromHTerm arg
fromHTerm (HDelay ann getTerm)    = Delay ann <$> (getTerm >>= fromHTerm)
fromHTerm (HForce ann term)       = Force ann <$> fromHTerm term
fromHTerm (HError ann)            = pure $ Error ann

fromValue
    :: Value unique name uni fun ann
    -> EvalM unique name uni fun ann (Term name uni fun ann)
fromValue = fromHTerm >=> bindFunM (const _builtinAppTerm)

runEvalM
    :: EvalM unique name uni fun ann a
    -> Either (HoasException (Term name uni fun ann)) a
runEvalM = bimap massageError id . unEvalM where
    -- !!!
    massageError = either id id . traverse (runEvalM . fromValue)

evalBuiltinApp
    :: ann
    -> EvalM unique name uni fun ann (Term name uni fun ann)
    -> BuiltinRuntime (Value unique name uni fun ann)
    -> EvalM unique name uni fun ann (Value unique name uni fun ann)
-- Note the absence of 'evalValue'. Same logic as with the CEK machine applies.
evalBuiltinApp _   _       (BuiltinRuntime (TypeSchemeResult _) _ x _) = makeKnown x
evalBuiltinApp ann getTerm runtime                                     =
    pure . HBuiltin ann $ BuiltinApp getTerm runtime

evalFeedBuiltinApp
    :: ann
    -> BuiltinApp unique name uni fun ann
    -> Maybe (Value unique name uni fun ann)
    -> EvalM unique name uni fun ann (Value unique name uni fun ann)
evalFeedBuiltinApp ann (BuiltinApp getTerm (BuiltinRuntime sch ar f _)) e =
    case (sch, e) of
        (TypeSchemeArrow _ schB, Just arg) -> do
            x <- readKnown arg
            evalBuiltinApp ann
                (Apply ann <$> getTerm <*> fromValue arg)
                (BuiltinRuntime schB ar (f x) undefined)
        (TypeSchemeAll  _ schK, Nothing) ->
            evalBuiltinApp ann
                (Force ann <$> getTerm)
                (BuiltinRuntime (schK Proxy) ar f undefined)
        _ ->
            throwingWithCause _InternalHoasError ArityHoasError Nothing

evalApply
    :: m ~ EvalM unique name uni fun ann
    => Value unique name uni fun ann
    -> Value unique name uni fun ann
    -> m (Value unique name uni fun ann)
evalApply (HLamAbs _ _ body) arg = body arg
evalApply (HBuiltin ann fun) arg = evalFeedBuiltinApp ann fun $ Just arg
evalApply term               _   =
    throwingWithCause _InternalHoasError TypeHoasError $ Just term

evalForce
    :: m ~ EvalM unique name uni fun ann
    => Value unique name uni fun ann
    -> m (Value unique name uni fun ann)
evalForce (HDelay _ term)    = term
evalForce (HBuiltin ann fun) = evalFeedBuiltinApp ann fun Nothing
evalForce term               =
    throwingWithCause _InternalHoasError TypeHoasError $ Just term

evalTerm
    :: forall term eterm unique name uni fun ann.
       ( term ~ Term name uni fun ann, eterm ~ Value unique name uni fun ann
       , HasUnique name unique, Ix fun
       )
    => BuiltinsRuntime fun eterm -> term -> EvalM unique name uni fun ann eterm
evalTerm (BuiltinsRuntime meanings) = go mempty where
    go
        :: UniqueMap unique (Value unique name uni fun ann)
        -> Term name uni fun ann
        -> EvalM unique name uni fun ann (Value unique name uni fun ann)
    go _   (Constant ann val) = pure $ HConstant ann val
    -- Using 'evalBuiltinApp' here would allow us to have named constants as builtins.
    -- Not that this is supported by anything else, though.
    go _   (Builtin ann fun) =
        -- TODO: proper error handling.
        pure . HBuiltin ann . BuiltinApp (pure $ Builtin ann fun) $ meanings ! fun
    go env (Var ann name) =
        case lookupName name env of
            Just term -> pure term
            Nothing   ->
                throwingWithCause _InternalHoasError UnexpectedVariableHoasError $
                    Just $ HVar ann name
    go env (LamAbs ann name body) =
        pure . HLamAbs ann name $ \arg -> go (insertByName name arg env) body
    go env (Apply _ fun arg) = do
        fun' <- go env fun
        arg' <- go env arg
        evalApply fun' arg'
    go env (Delay ann term) = pure . HDelay ann $ go env term  -- Laziness rulez.
    go env (Force _ term) = go env term >>= evalForce
    go _   (Error ann) = throwingWithCause _EvaluationFailure () . Just $ HError ann

evaluateHoas
    :: ( term ~ Term name uni fun ann, eterm ~ Value unique name uni fun ann
       , HasUnique name unique, Ix fun
       )
    => BuiltinsRuntime fun eterm -> term -> Either (HoasException term) term
evaluateHoas runtime term = runEvalM $ evalTerm runtime term >>= fromValue

unsafeEvaluateHoas
    :: ( term ~ Term name uni fun ann, eterm ~ Value unique name uni fun ann
       , HasUnique name unique, Ix fun
       , Typeable name, Typeable uni, Typeable fun, Typeable ann
       , PrettyPlc (Term name uni fun ann)
       )
    => BuiltinsRuntime fun eterm -> term -> EvaluationResult term
unsafeEvaluateHoas runtime = either throw id . extractEvaluationResult . evaluateHoas runtime
