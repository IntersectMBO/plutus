{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs                  #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE TemplateHaskell        #-}
{-# LANGUAGE TypeFamilies           #-}
{-# LANGUAGE UndecidableInstances   #-}

module Language.UntypedPlutusCore.HOAS where

import           Language.UntypedPlutusCore.Core

import           Language.PlutusCore.Constant
import           Language.PlutusCore.Evaluation.Machine.Exception
import           Language.PlutusCore.Evaluation.Result
import           Language.PlutusCore.Name
import           Language.PlutusCore.Pretty
import           Language.PlutusCore.Universe

import           Control.Concurrent.MVar
import           Control.Lens.TH
import           Control.Monad.Except
import           Data.Array
import           Data.Bifunctor
import           Data.Functor
import           Data.Proxy
import           System.IO.Unsafe

import           Language.PlutusCore.Builtins
import           Language.PlutusCore.StdLib.Data.ScottUnit

-- >>> import           Language.PlutusCore.Builtins
-- >>> import           Language.PlutusCore.StdLib.Data.ScottUnit
-- >>> import           Language.PlutusCore.Name
-- >>> import           Language.PlutusCore.Universe
-- >>> import           Language.UntypedPlutusCore.Core
-- >>> Right unitval :: Either () (Term Name DefaultUni DefaultFun ())
-- Right (Delay () (LamAbs () (Name {nameString = "x", nameUnique = Unique {unUnique = 1}}) (Var () (Name {nameString = "x", nameUnique = Unique {unUnique = 1}}))))
-- >>> evaluateHoas (unitval :: Term Name DefaultUni DefaultFun ())
-- Right (Delay () (LamAbs () (Name {nameString = "x", nameUnique = Unique {unUnique = 1}}) (Var () (Name {nameString = "x", nameUnique = Unique {unUnique = 1}}))))

data HTerm name uni fun ann
    = HConstant ann (Some (ValueOf uni))
    | HBuiltin ann fun
    | HVar ann name
    | HLamAbs ann name (HTerm name uni fun ann -> HTerm name uni fun ann)
    | HApply ann (HTerm name uni fun ann) (HTerm name uni fun ann)
    | HDelay ann (HTerm name uni fun ann)
    | HForce ann (HTerm name uni fun ann)
    | HError ann

type instance UniOf (HTerm name uni fun ann) = uni

instance AsConstant (HTerm name uni fun ann) where
    asConstant (HConstant _ val) = Just val
    asConstant _                 = Nothing

instance FromConstant (HTerm name uni fun ()) where
    fromConstant = HConstant ()

data FreeVariableError name ann = FreeVariableError ann name
    deriving (Show, Eq)

distributeLazily :: Functor f => (a -> f b) -> f (a -> b)
distributeLazily f = f x <&> \y x' -> unsafePerformIO $ y <$ tryPutMVar hole x' where
    hole = unsafePerformIO newEmptyMVar
    x = unsafePerformIO $ readMVar hole

toHTerm
    :: HasUnique name unique
    => Term name uni fun ann -> Either (FreeVariableError name ann) (HTerm name uni fun ann)
toHTerm = go mempty where
    go
        :: HasUnique name unique
        => UniqueMap unique (HTerm name uni fun ann)
        -> Term name uni fun ann
        -> Either (FreeVariableError name ann) (HTerm name uni fun ann)
    go _   (Constant ann val)     = pure $ HConstant ann val
    go _   (Builtin ann fun)      = pure $ HBuiltin ann fun
    go env (Var ann name)         =
        case lookupName name env of
            Nothing   -> Left $ FreeVariableError ann name
            Just term -> Right term
    go env (LamAbs ann name body) =
        -- That would require an explicit @Lazy@ wrapper, if we didn't use lazy @IntMap@s, I guess.
        HLamAbs ann name <$> distributeLazily (\var -> go (insertByName name var env) body)
    go env (Apply ann fun arg)    = HApply ann <$> go env fun <*> go env arg
    go env (Delay ann term)       = HDelay ann <$> go env term
    go env (Force ann term)       = HForce ann <$> go env term
    go _   (Error ann)            = pure (HError ann)

fromHTerm :: HTerm name uni fun ann -> Term name uni fun ann
fromHTerm (HConstant ann val)     = Constant ann val
fromHTerm (HBuiltin ann fun)      = Builtin ann fun
fromHTerm (HVar ann name)         = Var ann name
-- Here we don't recover the original annotation and instead use the one that the whole lambda
-- is annotated with. We could probably handle annotations better, but we don't care for now.
fromHTerm (HLamAbs ann name body) = LamAbs ann name . fromHTerm . body $ HVar ann name
fromHTerm (HApply ann fun arg)    = Apply ann (fromHTerm fun) (fromHTerm arg)
fromHTerm (HDelay ann term)       = Delay ann $ fromHTerm term
fromHTerm (HForce ann term)       = Force ann $ fromHTerm term
fromHTerm (HError ann)            = Error ann

instance PrettyBy config (Term name uni fun ann) => PrettyBy config (HTerm name uni fun ann) where
    prettyBy config = prettyBy config . fromHTerm

-- type EvalEnv name uni fun ann = BuiltinsRuntime fun (HTerm name uni fun ann)
-- type EvalM name uni fun ann = ReaderT (EvalEnv name uni fun ann) (Either ())

data EvalError name ann
    = UnexpectedVariable
    | UnliftingEvalError UnliftingError
    | ArityMismatch
    | FailureEvalError
    deriving (Show, Eq)

instance PrettyBy config (EvalError name ann) where
    prettyBy config = mempty

makeClassyPrisms ''EvalError

instance AsUnliftingError (EvalError name ann) where
    _UnliftingError = _UnliftingEvalError

type EvalException name uni fun ann = ErrorWithCause (EvalError name ann) (ETerm name uni fun ann)

freeVariableAsEvalException
    :: FreeVariableError name ann
    -> EvalException name uni fun ann
freeVariableAsEvalException (FreeVariableError ann name) =
    ErrorWithCause UnexpectedVariable . Just $ HVar ann name

instance AsEvaluationFailure (EvalError name ann) where
    _EvaluationFailure = _EvaluationFailureVia FailureEvalError

type EvalM name uni fun ann = Either (EvalException name uni fun ann)

data BuiltinApp name uni fun ann = BuiltinApp
    { _builtinAppTerm    :: Term name uni fun ann
    , _builtinAppRuntime :: BuiltinRuntime (ETerm name uni fun ann)
    }

instance Pretty (BuiltinApp name uni fun ann) where
    pretty _ = mempty

type ETerm name uni fun ann = HTerm name uni (BuiltinApp name uni fun ann) ann

toETerm
    :: (FromConstant (ETerm name DefaultUni DefaultFun ann), HasUnique name unique)
    => Term name DefaultUni DefaultFun ann
    -> Either (FreeVariableError name ann) (ETerm name DefaultUni DefaultFun ann)
toETerm = toHTerm . mapFun toBuiltinApp where
    BuiltinsRuntime meanings = defBuiltinsRuntime
    -- TODO: safe indexing.
    toBuiltinApp ann fun = BuiltinApp (Builtin ann fun) $ meanings ! fun

fromETerm :: ETerm name uni fun ann -> Term name uni fun ann
fromETerm = bindFun (const _builtinAppTerm) . fromHTerm

evalBuiltinApp :: ann -> BuiltinApp name uni fun ann -> EvalM name uni fun ann (ETerm name uni fun ann)
evalBuiltinApp ann ba@(BuiltinApp _ runtime) =
    case runtime of
        -- We have to call 'evalETerm' here, because @x@ can be an 'Opaque'.
        BuiltinRuntime (TypeSchemeResult _) _ x _ -> makeKnown x >>= evalETerm
        _                                         -> pure $ HBuiltin ann ba

evalFeedBuiltinApp
    :: ann
    -> BuiltinApp name uni fun ann
    -> Maybe (ETerm name uni fun ann)
    -> EvalM name uni fun ann (ETerm name uni fun ann)
evalFeedBuiltinApp ann (BuiltinApp term (BuiltinRuntime sch ar f _)) e = case (sch, e) of
    (TypeSchemeArrow _ schB, Just arg) -> do
        x <- readKnown arg
        evalBuiltinApp ann $ BuiltinApp
            (Apply ann term $ fromETerm arg)
            (BuiltinRuntime schB ar (f x) undefined)
    (TypeSchemeAll  _ schK, Nothing) ->
        evalBuiltinApp ann $ BuiltinApp
            (Force ann term)
            (BuiltinRuntime (schK Proxy) ar f undefined)
    _ ->
        throwingWithCause _EvalError ArityMismatch Nothing

evalApply
    :: ann
    -> ETerm name uni fun ann
    -> ETerm name uni fun ann
    -> EvalM name uni fun ann (ETerm name uni fun ann)
evalApply _   (HLamAbs _ _ body) arg = evalETerm $ body arg
evalApply _   (HBuiltin ann fun) arg = evalFeedBuiltinApp ann fun $ Just arg
evalApply ann fun                arg = pure $ HApply ann fun arg  -- TODO: or should that be an error?

evalForce :: ann -> ETerm name uni fun ann -> EvalM name uni fun ann (ETerm name uni fun ann)
evalForce _   (HDelay _ term)    = evalETerm term
evalForce _   (HBuiltin ann fun) = evalFeedBuiltinApp ann fun Nothing
evalForce ann del                = pure $ HForce ann del  -- TODO: or should that be an error?

evalETerm :: ETerm name uni fun ann -> EvalM name uni fun ann (ETerm name uni fun ann)
evalETerm (HConstant ann val)  = pure $ HConstant ann val
-- Using 'evalBuiltinApp' here allows us to have named constants as builtins.
-- Not that this is supported by everything else, though.
evalETerm (HBuiltin ann fun)   = evalBuiltinApp ann fun
evalETerm term@HVar{}          = throwingWithCause _EvalError UnexpectedVariable $ Just term
evalETerm term@HLamAbs{}       = pure term
evalETerm (HApply ann fun arg) = do
    fun' <- evalETerm fun
    arg' <- evalETerm arg
    evalApply ann fun' arg'
evalETerm term@HDelay{}        = pure term
evalETerm (HForce ann term)    = evalETerm term >>= evalForce ann
evalETerm term@(HError _)      = throwingWithCause _EvaluationFailure () $ Just term

evaluateHoas
    :: Term Name DefaultUni DefaultFun ()
    -> Either (EvalException Name DefaultUni DefaultFun ()) (Term Name DefaultUni DefaultFun ())
evaluateHoas = fmap fromETerm . evalETerm <=< first freeVariableAsEvalException . toETerm
