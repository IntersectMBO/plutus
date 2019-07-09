{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE GADTs #-}

module Language.PlutusCore.Constant.Typed where

import           Language.PlutusCore.Evaluation.Result
import           Language.PlutusCore.Constant.Universe
import           Language.PlutusCore.Lexer.Type
import           Language.PlutusCore.Name
import           Language.PlutusCore.Type
import           PlutusPrelude

import           Control.Monad.Except
import           Control.Monad.Morph                         as Morph
import           Control.Monad.Reader
import           Control.Monad.Trans.Inner
import           Data.Map                                    (Map)
import           Data.Proxy
import           Data.Text                                   (Text)
import           Control.Monad.Trans.Compose                 (ComposeT (..))
import           GHC.TypeLits

infixr 9 `TypeSchemeArrow`

-- instance Deep a => Deep (EvaluationResult a) where
--     toTypeAst _ = toTypeAst @a Proxy

--     liftDeep EvaluationFailure     = Error () $ toTypeAst @a Proxy
--     liftDeep (EvaluationSuccess x) = liftDeep x

--     unliftDeep eval = mapDeepReflectT (fmap $ EvaluationSuccess . sequence) . unliftDeep eval






type Evaluator uni f m
    =  DynamicBuiltinNameMeanings uni
    -> f TyName Name uni ()
    -> m (EvaluationResultDef uni)

newtype EvaluateT uni t m a = EvaluateT
    { unEvaluateT :: ReaderT (Evaluator uni Term m) (t m) a
    } deriving
        ( Functor, Applicative, Monad, Alternative, MonadPlus
        , MonadError e
        )

-- | Run an 'EvaluateT' computation using the given 'Evaluator'.
runEvaluateT :: Evaluator uni Term m -> EvaluateT uni t m a -> t m a
runEvaluateT eval (EvaluateT a) = runReaderT a eval

-- | Wrap a computation binding an 'Evaluator' as a 'EvaluateT'.
withEvaluator :: (Evaluator uni Term m -> t m a) -> EvaluateT uni t m a
withEvaluator = EvaluateT . ReaderT

-- | 'thoist' for monad transformer transformers is what 'hoist' for monad transformers.
thoist :: Monad (t m) => (forall b. t m b -> s m b) -> EvaluateT uni t m a -> EvaluateT uni s m a
thoist f (EvaluateT a) = EvaluateT $ Morph.hoist f a



newtype ReflectT m a = ReflectT
    { unReflectT :: ExceptT Text (InnerT EvaluationResult m) a
    } deriving
        ( Functor, Applicative, Monad
        , MonadError Text
        )
      deriving MonadTrans via ComposeT (ExceptT Text) (InnerT EvaluationResult)

-- Uses the 'Alternative' instance of 'EvaluationResult'.
instance Monad m => Alternative (ReflectT m) where
    empty = ReflectT . lift $ yield empty
    ReflectT (ExceptT (InnerT m)) <|> ReflectT (ExceptT (InnerT n)) =
        ReflectT . ExceptT . InnerT $ (<|>) <$> m <*> n

runReflectT :: ReflectT m a -> m (EvaluationResult (Either Text a))
runReflectT = unInnerT . runExceptT . unReflectT

mapReflectT
    :: (ExceptT Text (InnerT EvaluationResult m) a -> ExceptT Text (InnerT EvaluationResult n) b)
    -> ReflectT m a
    -> ReflectT n b
mapReflectT f (ReflectT a) = ReflectT (f a)

mapDeepReflectT
    :: (m (EvaluationResult (Either Text a)) -> n (EvaluationResult (Either Text b)))
    -> ReflectT m a
    -> ReflectT n b
mapDeepReflectT = mapReflectT . mapExceptT . mapInnerT



-- See Note [Semantics of dynamic built-in types].
-- See Note [Converting PLC values to Haskell values].
-- | Haskell types known to exist on the PLC side.
class KnownType a where
    -- | The type representing @a@ used on the PLC side.
    toTypeAst :: proxy a -> Type TyName ()

    -- | Convert a Haskell value to the corresponding PLC value.
    makeKnown :: a -> Term TyName Name ()

    -- See Note [Evaluators].
    -- | Convert a PLC value to the corresponding Haskell value using an explicit evaluator.
    readKnown :: Monad m => Evaluator Term m -> Term TyName Name () -> ReflectT m a

    -- | Pretty-print a value of a 'KnownType' in a PLC-specific way
    -- (see e.g. the @ByteString@ instance).
    prettyKnown :: a -> Doc ann
    default prettyKnown :: Pretty a => a -> Doc ann
    prettyKnown = pretty

class KnownType a where
    toTypeAst :: proxy a -> Type TyName uni ()
    makeKnown :: a -> Term TyName Name con ()
    readKnown :: Monad m => Evaluator uni Term m -> Term TyName Name uni () -> ReflectT m a

readKnownM :: (Monad m, KnownType a) => Term TyName Name uni () -> EvaluateT uni ReflectT m a
readKnownM term = withEvaluator $ \eval -> readKnown eval term



newtype OpaqueTerm uni (text :: Symbol) (unique :: Nat) = OpaqueTerm
    { unOpaqueTerm :: Term TyName Name uni ()
    }

data TypeScheme uni a r where
    TypeSchemeResult :: uni `Includes` a => Proxy a -> TypeScheme uni a a
    -- TODO: delete @KnownType a@ once implicit unlifting is gone.
    TypeSchemeArrow
        :: (uni `Includes` a, KnownType a)
        => Proxy a -> TypeScheme uni b r -> TypeScheme uni (a -> b) r
    TypeSchemeAllType
        :: (KnownSymbol text, KnownNat uniq)
        => Proxy '(text, uniq)
        -> (forall ot. ot ~ OpaqueTerm uni text uniq => Proxy ot -> TypeScheme uni a r)
        -> TypeScheme uni a r

-- | A 'BuiltinName' with an associated 'TypeScheme'.
data TypedBuiltinName uni a r = TypedBuiltinName BuiltinName (TypeScheme uni a r)

data DynamicBuiltinNameMeaning uni =
    forall a r. DynamicBuiltinNameMeaning (TypeScheme uni a r) a

newtype DynamicBuiltinNameMeanings uni = DynamicBuiltinNameMeanings
    { unDynamicBuiltinNameMeanings :: Map DynamicBuiltinName (DynamicBuiltinNameMeaning uni)
    } deriving (Semigroup, Monoid)



-- typedTakeByteString
--     :: (uni `Includes` Integer, uni `Includes` BSL.ByteString)
--     => TypedBuiltinName uni (Integer -> BSL.ByteString -> BSL.ByteString) BSL.ByteString
-- typedTakeByteString =
--     TypedBuiltinName TakeByteString $
--         Proxy `TypeSchemeArrow` Proxy `TypeSchemeArrow` TypeSchemeResult Proxy



-- unlift :: Evaluator -> Term uni -> a

-- unliftList list = unwrap list $[] (\{_} x xs -> $(:) x (unliftList xs))
-- @unliftList@ turns the deep embedding of @[]@ into the shallow embedding and from there we can
-- just perform a single pattern match.
-- NO LONGER NEED @Evaluator@???
-- But with @Evaluator@ we could unlift values lazily, right? Is that important, though?

-- Should we be able to apply Haskell's @reverse :: forall a. [a] -> [a]@ to a PLC's list?
-- [a] -> list a  -- does not require an evaluator
-- list a -> [a]  -- requires an evaluator currently
-- Do we only need evaluators for implicit conversions?

-- User provides PLC->Haskell, we derive Haskell->PLC?
