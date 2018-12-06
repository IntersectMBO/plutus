{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE KindSignatures    #-}
{-# LANGUAGE PolyKinds         #-}
{-# LANGUAGE TemplateHaskell   #-}
{-# OPTIONS_GHC -Wno-orphans #-}
module Language.PlutusTx.Lift.Instances () where

import qualified Language.PlutusCore          as PLC

import           Language.PlutusTx.Lift.Class
import           Language.PlutusTx.Utils

import           Language.PlutusIR

import qualified Data.ByteString.Lazy         as BSL
import           Data.Proxy

-- Derived instances

-- This instance ensures that we can apply typeable type constructors to typeable arguments and get a typeable
-- type. We need the kind variable, so that partial application of type constructors works.
instance (Typeable (f :: * -> k), Typeable (a :: *)) => Typeable (f a) where
    typeRep _ = TyApp () <$> typeRep (undefined :: Proxy f) <*> typeRep (undefined :: Proxy a)

instance (Typeable (a :: *), Typeable (b :: *)) => Typeable (a -> b) where
    typeRep _ = TyFun () <$> typeRep (undefined :: Proxy a) <*> typeRep (undefined :: Proxy b)

-- Primitives

instance Typeable Int where
    typeRep _ = pure $ appSize haskellIntSize (TyBuiltin () PLC.TyInteger)

instance Lift Int where
    lift i = pure $ Constant () $ PLC.BuiltinInt () haskellIntSize $ fromIntegral i

instance Typeable BSL.ByteString where
    typeRep _ = pure $ appSize haskellBSSize (TyBuiltin () PLC.TyByteString)

instance Lift BSL.ByteString where
    lift bs = pure $ Constant () $ PLC.BuiltinBS () haskellBSSize bs

-- Standard types
-- These need to be in a separate file for TH staging reasons

makeLift ''Bool
makeLift ''Maybe
makeLift ''Either
makeLift ''[]
-- include a few tuple instances for convenience
makeLift ''(,)
makeLift ''(,,)
makeLift ''(,,,)
makeLift ''(,,,,)
