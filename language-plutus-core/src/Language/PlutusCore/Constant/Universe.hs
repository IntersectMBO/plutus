{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE GADTs #-}

module Language.PlutusCore.Constant.Universe where

import           Language.PlutusCore.Evaluation.Result
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
import qualified Data.ByteString.Lazy as BSL

infixr 9 `TypeSchemeArrow`

data ValueIn uni = forall a. ValueIn (uni a) a

-- We probably want to use that together with `fastsum`.
-- But also allow @Either@ and use type families for computing the index of a type,
-- because we want to extend @uni@ in order to unlift values.
class uni `Includes` a where
    uniVal :: uni a

data TypeScheme uni a r where
    TypeSchemeResult :: uni `Includes` a => Proxy a -> TypeScheme uni a a
    TypeSchemeArrow  :: uni `Includes` a => Proxy a -> TypeScheme uni b r -> TypeScheme uni (a -> b) r

-- | A 'BuiltinName' with an associated 'TypeScheme'.
data TypedBuiltinName uni a r = TypedBuiltinName BuiltinName (TypeScheme uni a r)

data DynamicBuiltinNameMeaning uni =
    forall a r. DynamicBuiltinNameMeaning (TypeScheme uni a r) a

newtype DynamicBuiltinNameMeanings uni = DynamicBuiltinNameMeanings
    { unDynamicBuiltinNameMeanings :: Map DynamicBuiltinName (DynamicBuiltinNameMeaning uni)
    } deriving (Semigroup, Monoid)

type Evaluator uni f m
    =  DynamicBuiltinNameMeanings uni
    -> f TyName Name (ValueIn uni) ()
    -> m (EvaluationResultDef (ValueIn uni))

newtype EvaluateT uni t m a = EvaluateT
    { unEvaluateT :: ReaderT (Evaluator uni Term m) (t m) a
    } deriving
        ( Functor, Applicative, Monad, Alternative, MonadPlus
--         , MonadReader (Evaluator uni Term m)
        , MonadError e
        )

-- | Run an 'EvaluateT' computation using the given 'Evaluator'.
runEvaluateT :: Evaluator uni Term m -> EvaluateT uni t m a -> t m a
runEvaluateT eval (EvaluateT a) = runReaderT a eval



typedTakeByteString
    :: (uni `Includes` Integer, uni `Includes` BSL.ByteString)
    => TypedBuiltinName uni (Integer -> BSL.ByteString -> BSL.ByteString) BSL.ByteString
typedTakeByteString =
    TypedBuiltinName TakeByteString $
        Proxy `TypeSchemeArrow` Proxy `TypeSchemeArrow` TypeSchemeResult Proxy

-- unlift :: Evaluator -> Term uni -> a

-- unliftList list = unwrap list $[] (\{_} x xs -> $(:) x (unliftList xs))
-- @unliftList@ turns the deep embedding of @[]@ into the shallow embedding and from there we can
-- just perform a single pattern match.
-- NO LONGER NEED @Evaluator@???
-- But with @Evaluator@ we could unlift values lazily, right? Is that important, though?

-- Should we be able to apply Haskell's @reverse :: forall a. [a] -> [a]@ to a PLC's list?

-- User provides PLC->Haskell, we derive Haskell->PLC?

-- data CekEnv uni = CekEnv
--     { ...
--     , _cekEnvEmbVals :: UniqueMap TermUnique (ValueIn uni)
--     }

-- computeCek :: GEq uni => Context -> Plain Term -> CekM uni EvaluationResultDef

-- type Evaluator f m = DynamicBuiltinNameMeanings -> f TyName Name () -> m EvaluationResultDef
-- readKnown :: Monad m => Evaluator Term m -> Term TyName Name () -> ReflectT m a


-- -- | Typed 'TakeByteString'.
-- typedTakeByteString :: TypedBuiltinName (Integer -> BSL.ByteString -> BSL.ByteString) BSL.ByteString
-- typedTakeByteString =
--     TypedBuiltinName TakeByteString $
--         Proxy `TypeSchemeArrow` Proxy `TypeSchemeArrow` TypeSchemeResult Proxy

-- data Term tyname name con ann
--     = ...
--     | Pure ext

-- type ExtTerm tyname name uni ann = Term tyname name (exists a. (uni a, a)) ann

-- evaluateCk :: GEq uni => ExtTerm tyname name uni ann -> ExtTerm tyname name uni ann

-- data Typed uni a r where
--     ...
--     TypeSchemeResult :: uni `Includes` a => Proxy a -> TypeScheme a a
--     TypeSchemeArrow  :: uni `Includes` a => Proxy a -> TypeScheme b r -> TypeScheme (a -> b) r

-- -- We probably want to use that together with `fastsum`.
-- -- But also allow @Either@ and use type families for computing the index of a type,
-- -- because we want to extend @uni@ in order to unlift values.
-- class uni `Includes` a where
--     uniVal :: uni a

-- typedTakeByteString
--     :: (uni `Includes` Integer, uni `Includes` ByteString)
--     => TypedBuiltinName uni (Integer -> ByteString -> ByteString)
-- typedTakeByteString =
--     TypedBuiltinName TakeByteString $
--         Proxy `TypeSchemeArrow` Proxy `TypeSchemeArrow` TypeSchemeResult Proxy
