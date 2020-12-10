{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs                  #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE OverloadedStrings      #-}
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
import           Control.Exception
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

-- distributeLazily :: Functor f => (a -> f b) -> f (a -> b)
-- distributeLazily f = f x <&> \y x' -> unsafePerformIO $ y <$ tryPutMVar hole x' where
--     hole = unsafePerformIO newEmptyMVar
--     x = unsafePerformIO $ readMVar hole

-- toHTerm
--     :: HasUnique name unique
--     => Term name uni fun ann -> Either (FreeVariableError name ann) (HTerm name uni fun ann)
-- toHTerm = go mempty where
--     go
--         :: HasUnique name unique
--         => UniqueMap unique (HTerm name uni fun ann)
--         -> Term name uni fun ann
--         -> Either (FreeVariableError name ann) (HTerm name uni fun ann)
--     go _   (Constant ann val)     = pure $ HConstant ann val
--     go _   (Builtin ann fun)      = pure $ HBuiltin ann fun
--     go env (Var ann name)         =
--         case lookupName name env of
--             Nothing   -> Left $ FreeVariableError ann name
--             Just term -> Right term
--     go env (LamAbs ann name body) =
--         -- That would require an explicit @Lazy@ wrapper, if we didn't use lazy @IntMap@s, I guess.
--         HLamAbs ann name <$> distributeLazily (\var -> go (insertByName name var env) body)
--     go env (Apply ann fun arg)    = HApply ann <$> go env fun <*> go env arg
--     go env (Delay ann term)       = HDelay ann <$> go env term
--     go env (Force ann term)       = HForce ann <$> go env term
--     go _   (Error ann)            = pure (HError ann)

toHTerm
    :: HasUnique name unique
    => Term name uni fun ann -> Either (FreeVariableError name ann) (HTerm name uni fun ann)
toHTerm = pure . go mempty where
    go
        :: HasUnique name unique
        => UniqueMap unique (HTerm name uni fun ann)
        -> Term name uni fun ann
        -> HTerm name uni fun ann
    go _   (Constant ann val)     = HConstant ann val
    go _   (Builtin ann fun)      = HBuiltin ann fun
    go env (Var ann name)         =
        case lookupName name env of
            Nothing   -> error "free variable" -- throw $ FreeVariableError ann name
            Just term -> term
    go env (LamAbs ann name body) =
        -- That would require an explicit @Lazy@ wrapper, if we didn't use lazy @IntMap@s, I guess.
        HLamAbs ann name $ \var -> go (insertByName name var env) body
    go env (Apply ann fun arg)    = HApply ann (go env fun) (go env arg)
    go env (Delay ann term)       = HDelay ann $ go env term
    go env (Force ann term)       = HForce ann $ go env term
    go _   (Error ann)            = HError ann

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

data UserHoasError
    = HoasEvaluationFailure
    deriving (Show, Eq)

data InternalHoasError
    = UnexpectedVariableHoasError
    | UnliftingHoasError UnliftingError
    | ArityHoasError
    | TypeHoasError
    deriving (Show, Eq)

makeClassyPrisms ''UserHoasError
makeClassyPrisms ''InternalHoasError

instance AsInternalHoasError internal => AsInternalHoasError (EvaluationError user internal) where
    _InternalHoasError = _InternalEvaluationError . _InternalHoasError

instance PrettyBy config UserHoasError where
    prettyBy _ HoasEvaluationFailure = "EvaluationFailure"

instance PrettyBy config InternalHoasError where
    prettyBy _ = pretty . show

instance AsUnliftingError InternalHoasError where
    _UnliftingError = _UnliftingHoasError

type HoasException name uni fun ann =
    EvaluationException UserHoasError InternalHoasError (Term name uni fun ann)

freeVariableAsHoasException
    :: FreeVariableError name ann
    -> HoasException name uni fun ann
freeVariableAsHoasException (FreeVariableError ann name) =
    ErrorWithCause (InternalEvaluationError UnexpectedVariableHoasError) . Just $ Var ann name

instance AsEvaluationFailure UserHoasError where
    _EvaluationFailure = _EvaluationFailureVia HoasEvaluationFailure

type EvalM name uni fun ann = Either (HoasException name uni fun ann)

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

evalBuiltinApp
    :: ann
    -> Term name uni fun ann
    -> BuiltinRuntime (ETerm name uni fun ann)
    -> EvalM name uni fun ann (ETerm name uni fun ann)
-- Note the absence of 'evalETerm'. Same logic as with the CEK machine applies.
evalBuiltinApp _   _    (BuiltinRuntime (TypeSchemeResult _) _ x _) = makeKnown x
evalBuiltinApp ann term runtime                                     =
    pure . HBuiltin ann $ BuiltinApp term runtime

evalFeedBuiltinApp
    :: ann
    -> BuiltinApp name uni fun ann
    -> Maybe (ETerm name uni fun ann)
    -> EvalM name uni fun ann (ETerm name uni fun ann)
evalFeedBuiltinApp ann (BuiltinApp term (BuiltinRuntime sch ar f _)) e =
    case (sch, e) of
        (TypeSchemeArrow _ schB, Just arg) -> do
            x <- first (fmap fromETerm) $ readKnown arg
            evalBuiltinApp ann
                (Apply ann term $ fromETerm arg)
                (BuiltinRuntime schB ar (f x) undefined)
        (TypeSchemeAll  _ schK, Nothing) ->
            evalBuiltinApp ann
                (Force ann term)
                (BuiltinRuntime (schK Proxy) ar f undefined)
        _ ->
            throwingWithCause _InternalHoasError ArityHoasError Nothing

evalApply
    :: ETerm name uni fun ann
    -> ETerm name uni fun ann
    -> EvalM name uni fun ann (ETerm name uni fun ann)
evalApply (HLamAbs _ _ body) arg = evalETerm $ body arg
evalApply (HBuiltin ann fun) arg = evalFeedBuiltinApp ann fun $ Just arg
evalApply term               _   =
    throwingWithCause _InternalHoasError TypeHoasError . Just $ fromETerm term

evalForce :: ETerm name uni fun ann -> EvalM name uni fun ann (ETerm name uni fun ann)
evalForce (HDelay _ term)    = evalETerm term
evalForce (HBuiltin ann fun) = evalFeedBuiltinApp ann fun Nothing
evalForce term               =
    throwingWithCause _InternalHoasError TypeHoasError . Just $ fromETerm term

evalETerm :: ETerm name uni fun ann -> EvalM name uni fun ann (ETerm name uni fun ann)
evalETerm term@HConstant{}   = pure term
-- Using 'evalBuiltinApp' here would allows us to have named constants as builtins.
-- Not that this is supported by anything else, though.
evalETerm term@HBuiltin{}    = pure term
evalETerm (HVar ann name)    =
    throwingWithCause _InternalHoasError UnexpectedVariableHoasError . Just $ Var ann name
evalETerm term@HLamAbs{}     = pure term
evalETerm (HApply _ fun arg) = do
    fun' <- evalETerm fun
    arg' <- evalETerm arg
    evalApply fun' arg'
evalETerm term@HDelay{}      = pure term
evalETerm (HForce _ term)    = evalETerm term >>= evalForce
evalETerm (HError ann)       = throwingWithCause _EvaluationFailure () . Just $ Error ann

evaluateHoas
    :: Term Name DefaultUni DefaultFun ()
    -> Either (HoasException Name DefaultUni DefaultFun ()) (Term Name DefaultUni DefaultFun ())
evaluateHoas = fmap fromETerm . evalETerm <=< first freeVariableAsHoasException . toETerm

unsafeEvaluateHoas
    :: Term Name DefaultUni DefaultFun ()
    -> EvaluationResult (Term Name DefaultUni DefaultFun ())
unsafeEvaluateHoas = either throw id . extractEvaluationResult . evaluateHoas
