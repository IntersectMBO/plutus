{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE OverloadedStrings      #-}
{-# LANGUAGE TemplateHaskell        #-}
{-# LANGUAGE TypeApplications       #-}
{-# LANGUAGE TypeFamilies           #-}
{-# LANGUAGE UndecidableInstances   #-}

module Language.UntypedPlutusCore.Evaluation.HOAS
    ( HTerm
    , UserHoasError (..)
    , InternalHoasError (..)
    , HoasException
    , Value
    , BuiltinApp
    , EvalM
    , evaluateHoas
    , unsafeEvaluateHoas
    ) where

import           Language.UntypedPlutusCore.Core

import           Language.PlutusCore.Constant                     hiding (lookupBuiltin)
import           Language.PlutusCore.Evaluation.Machine.Exception
import           Language.PlutusCore.Evaluation.Result
import           Language.PlutusCore.Name
import           Language.PlutusCore.Pretty
import           Language.PlutusCore.Universe

import           Control.Exception
import           Control.Lens                                     (ix, (^?))
import           Control.Lens.TH
import           Control.Monad.Except
import           Data.Array
import           Data.Bifunctor
import           Data.Proxy
import           Data.Typeable

-- | A higher-order version of 'Term'.
data HTerm m name uni fun ann
    = HConstant ann (Some (ValueOf uni))
    | HBuiltin ann fun
    | HVar ann name
    | HLamAbs ann name (HTerm m name uni fun ann -> m (HTerm m name uni fun ann))
    | HApply ann (HTerm m name uni fun ann) (HTerm m name uni fun ann)
    -- @(->) ()@ is to make sure the body of a 'Delay' does not get evaluated before the 'Delay'
    -- is forced. Laziness would already save us, but it's worth being explicit, hence the dummy
    -- argument.
    | HDelay ann (() -> m (HTerm m name uni fun ann))
    | HForce ann (HTerm m name uni fun ann)
    | HError ann

type instance UniOf (HTerm m name uni fun ann) = uni

instance AsConstant (HTerm m name uni fun ann) where
    asConstant (HConstant _ val) = Just val
    asConstant _                 = Nothing

instance FromConstant (HTerm m name uni fun ()) where
    fromConstant = HConstant ()

data UserHoasError
    = HoasEvaluationFailure
    deriving (Show, Eq)

-- Those perhaps shouldn't be called "internal". The user can easily trigger the first three by
-- uploading the wrong thing. But then we have the same issue with the CEK machine where
-- 'MachineError' is not that internal as well.
data InternalHoasError fun
    = FreeVariableHoasError
    | UnliftingHoasError UnliftingError
    | ArityHoasError
    | UnknownBuiltinHoasError fun
    deriving (Show, Eq, Functor)

instance PrettyBy PrettyConfigPlc UserHoasError where
    prettyBy _ HoasEvaluationFailure = "EvaluationFailure"

instance Pretty fun => PrettyBy config (InternalHoasError fun) where
    prettyBy _ = pretty . show . fmap (display @String)

type HoasException fun = EvaluationException UserHoasError (InternalHoasError fun)

instance AsEvaluationFailure UserHoasError where
    _EvaluationFailure = _EvaluationFailureVia HoasEvaluationFailure

-- | A 'Value' is an 'HTerm' being evaluatated in the 'EvalM' monad and with built-in functions
-- mapped to their (possibly partially applied) meanings.
type Value unique name uni fun ann =
    HTerm (EvalM unique name uni fun ann) name uni (BuiltinApp unique name uni fun ann) ann

-- | A builtin application consists of a (possibly partially applied) built-in function and
-- a delayed computation returning the 'Term' representation of that builtin, which we need
-- in case the built-in function never gets fully saturated, which requires us to put the
-- builtin into the resulting term.
data BuiltinApp unique name uni fun ann = BuiltinApp
    { _builtinAppTerm    :: EvalM unique name uni fun ann (Term name uni fun ann)
    , _builtinAppRuntime :: BuiltinRuntime (Value unique name uni fun ann)
    }

-- 'EvalM' is referenced in 'Value', so 'EvalM' is recursive and hence it has to be a @newtype@.
-- | The monad the HOAS evaluator runs in.
newtype EvalM unique name uni fun ann a = EvalM
    { unEvalM :: Either (HoasException fun (Value unique name uni fun ann)) a
    } deriving newtype
        ( Functor, Applicative, Monad
        , MonadError (HoasException fun (Value unique name uni fun ann))
        )

makeClassyPrisms ''UserHoasError
makeClassyPrisms ''InternalHoasError

instance AsInternalHoasError internal fun =>
            AsInternalHoasError (EvaluationError user internal) fun where
    _InternalHoasError = _InternalEvaluationError . _InternalHoasError
instance AsUnliftingError (InternalHoasError fun) where
    _UnliftingError = _UnliftingHoasError

-- | Convert an 'HTerm' into a 'Term' running all internal monadic actions along the way.
fromHTerm :: Monad m => HTerm m name uni fun ann -> m (Term name uni fun ann)
fromHTerm (HConstant ann val)     = pure $ Constant ann val
fromHTerm (HBuiltin ann fun)      = pure $ Builtin ann fun
fromHTerm (HVar ann name)         = pure $ Var ann name
-- Here we do not recover the original annotation and instead use the one that the whole lambda
-- is annotated with. We could probably handle annotations better, but we don't care for now.
fromHTerm (HLamAbs ann name body) = LamAbs ann name <$> (body (HVar ann name) >>= fromHTerm)
fromHTerm (HApply ann fun arg)    = Apply ann <$> fromHTerm fun <*> fromHTerm arg
fromHTerm (HDelay ann getBody)    = Delay ann <$> (getBody () >>= fromHTerm)
fromHTerm (HForce ann term)       = Force ann <$> fromHTerm term
fromHTerm (HError ann)            = pure $ Error ann

-- | Convert a 'Value' into a 'Term' running all internal monadic actions along the way and
-- extracting all partial builtin applications.
fromValue
    :: Value unique name uni fun ann
    -> EvalM unique name uni fun ann (Term name uni fun ann)
fromValue = fromHTerm >=> bindFunM (const _builtinAppTerm)

-- | Run an 'EvalM' computation and convert the cause of a possible error from 'Value' to 'Term'.
runEvalM
    :: EvalM unique name uni fun ann a
    -> Either (HoasException fun (Term name uni fun ann)) a
runEvalM = bimap errorValueToTerm id . unEvalM where
    -- Here we call 'runEvalM' recursively. It's fine when the underlying monad is 'Either',
    -- but if it had 'ReaderT', then we'd also need to make sure that 'runEvalM' is supplied
    -- with the most recent environment, not the initial one.
    errorValueToTerm = either id id . traverse (runEvalM . fromValue)

lookupVar
    :: HasUnique name unique
    => ann -> name -> UniqueMap unique value -> EvalM unique name uni fun ann value
lookupVar ann name env =
    case lookupName name env of
        Just term -> pure term
        Nothing   ->
            throwingWithCause _InternalHoasError FreeVariableHoasError $
                Just $ HVar ann name

-- | Retrieve the meaning of a built-in function.
lookupBuiltin
    :: (value ~ Value unique name uni fun ann, Ix fun)
    => ann -> fun -> BuiltinsRuntime fun value -> EvalM unique name uni fun ann value
lookupBuiltin ann fun (BuiltinsRuntime meanings) =
    case meanings ^? ix fun of
        Nothing      -> throwingWithCause _InternalHoasError (UnknownBuiltinHoasError fun) Nothing
        Just meaning -> pure . HBuiltin ann $ BuiltinApp (pure $ Builtin ann fun) meaning

-- | Take pieces of a 'BuiltinApp' and either create a 'Value' using 'makeKnown' or a partial
-- builtin application depending on whether the built-in function is fully saturated or not.
evalBuiltinApp
    :: ann
    -> EvalM unique name uni fun ann (Term name uni fun ann)
    -> BuiltinRuntime (Value unique name uni fun ann)
    -> EvalM unique name uni fun ann (Value unique name uni fun ann)
-- Note the absence of 'evalValue'. Same logic as with the CEK machine applies: 'makeKnown' never
-- returns a non-value term.
evalBuiltinApp _   _       (BuiltinRuntime (TypeSchemeResult _) _ x _) = makeKnown x
evalBuiltinApp ann getTerm runtime                                     =
    pure . HBuiltin ann $ BuiltinApp getTerm runtime

-- | Either 'Apply' or 'Force' a (possibly partially applied) built-in function depending on
--
-- 1. what the builtin expects
-- 2. whether the 'Maybe' argument is a 'Just' or 'Nothing'
--
-- (the two answers must agree, otherwise we have an error) and invoke 'evalBuiltinApp'.
evalFeedBuiltinApp
    :: ann
    -> BuiltinApp unique name uni fun ann
    -> Maybe (Value unique name uni fun ann)
    -> EvalM unique name uni fun ann (Value unique name uni fun ann)
evalFeedBuiltinApp ann (BuiltinApp getTerm (BuiltinRuntime sch ar f _)) e =
    case (sch, e) of
        (TypeSchemeArrow _ schB, Just arg) -> do
            x <- readKnown arg
            evalBuiltinApp
                ann
                (Apply ann <$> getTerm <*> fromValue arg)
                (BuiltinRuntime schB ar (f x) noCosting)
        (TypeSchemeAll  _ schK, Nothing) ->
            evalBuiltinApp
                ann
                (Force ann <$> getTerm)
                (BuiltinRuntime (schK Proxy) ar f noCosting)
        _ ->
            throwingWithCause _InternalHoasError ArityHoasError Nothing
  where
    -- I guess we could use a no-costing version of 'BuiltinRuntime', but I prefer to reuse
    -- the existing one even if it means throwing an error on any attempt to do something
    -- involving costs. Especially since it's planned to support costing in the HOAS evaluator.
    noCosting = error "HOAS currently does not support costing"

{- Note [Partial applications]
evalApply evalForce
-}

-- | Evaluate the application of a function to a value.
evalApply
    :: ann
    -> Value unique name uni fun ann
    -> Value unique name uni fun ann
    -> EvalM unique name uni fun ann (Value unique name uni fun ann)
evalApply _   (HLamAbs _ _ body) arg = body arg
evalApply _   (HBuiltin ann fun) arg = evalFeedBuiltinApp ann fun $ Just arg
evalApply ann fun                arg = pure $ HApply ann fun arg

-- | Force a delayed computation.
evalForce
    :: ann
    -> Value unique name uni fun ann
    -> EvalM unique name uni fun ann (Value unique name uni fun ann)
evalForce _   (HDelay _ getBody) = getBody ()
evalForce _   (HBuiltin ann fun) = evalFeedBuiltinApp ann fun Nothing
evalForce ann term               = pure $ HForce ann term

-- | Evaluate a 'Term' in the 'EvalM' monad using HOAS.
evalTerm
    :: forall term value unique name uni fun ann.
       ( term ~ Term name uni fun ann, value ~ Value unique name uni fun ann
       , HasUnique name unique, Ix fun
       )
    => BuiltinsRuntime fun value -> term -> EvalM unique name uni fun ann value
evalTerm runtime = go mempty where
    go
        :: UniqueMap unique value
        -> Term name uni fun ann
        -> EvalM unique name uni fun ann value
    go _   (Constant ann val) = pure $ HConstant ann val
    -- Using 'evalBuiltinApp' here would allow us to have named constants as builtins.
    -- Not that this is supported by anything else, though.
    go _   (Builtin ann fun) = lookupBuiltin ann fun runtime
    go env (Var ann name) = lookupVar ann name env
    go env (LamAbs ann name body) =
        pure . HLamAbs ann name $ \arg -> go (insertByName name arg env) body
    go env (Apply ann fun arg) = do
        fun' <- go env fun
        arg' <- go env arg
        evalApply ann fun' arg'
    go env (Delay ann term) = pure . HDelay ann $ \() -> go env term
    go env (Force ann term) = go env term >>= evalForce ann
    go _   (Error ann) = throwingWithCause _EvaluationFailure () . Just $ HError ann

-- | Evaluate a term using the HOAS evaluator.
evaluateHoas
    :: ( term ~ Term name uni fun ann, value ~ Value unique name uni fun ann
       , HasUnique name unique, Ix fun
       )
    => BuiltinsRuntime fun value -> term -> Either (HoasException fun term) term
evaluateHoas runtime term = runEvalM $ evalTerm runtime term >>= fromValue

-- | Evaluate a term using the HOAS evaluator. May throw a 'HoasException'.
unsafeEvaluateHoas
    :: ( term ~ Term name uni fun ann, value ~ Value unique name uni fun ann
       , HasUnique name unique, Ix fun
       , Typeable name, Typeable uni, Typeable fun, Typeable ann
       , Pretty fun, PrettyPlc (Term name uni fun ann)
       )
    => BuiltinsRuntime fun value -> term -> EvaluationResult term
unsafeEvaluateHoas runtime = either throw id . extractEvaluationResult . evaluateHoas runtime
