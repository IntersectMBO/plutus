{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE KindSignatures    #-}
{-# LANGUAGE PolyKinds         #-}
{-# LANGUAGE TemplateHaskell   #-}
{-# OPTIONS_GHC -Wno-orphans #-}
module Language.Plutus.Lift.Instances () where

import qualified Language.PlutusCore             as PLC

import           Language.Plutus.CoreToPLC.Utils
import           Language.Plutus.Lift.LiftPir
import           Language.PlutusIR

import qualified Data.ByteString.Lazy            as BSL
import           Data.Proxy

-- Derived instances

-- This instance ensures that we can apply typeable type constructors to typeable arguments and get a typeable
-- type. We need the kind variable, so that partial application of type constructors works.
instance (TypeablePir (f :: * -> k), TypeablePir (a :: *)) => TypeablePir (f a) where
    typeRep _ = TyApp () <$> typeRep (undefined :: Proxy f) <*> typeRep (undefined :: Proxy a)

instance (TypeablePir (a :: *), TypeablePir (b :: *)) => TypeablePir (a -> b) where
    typeRep _ = TyFun () <$> typeRep (undefined :: Proxy a) <*> typeRep (undefined :: Proxy b)

-- Primitives

instance TypeablePir Int where
    typeRep _ = pure $ appSize haskellIntSize (TyBuiltin () PLC.TyInteger)

instance LiftPir Int where
    lift i = pure $ Constant () $ PLC.BuiltinInt () haskellIntSize $ fromIntegral i

instance TypeablePir BSL.ByteString where
    typeRep _ = pure $ appSize haskellBSSize (TyBuiltin () PLC.TyByteString)

instance LiftPir BSL.ByteString where
    lift bs = pure $ Constant () $ PLC.BuiltinBS () haskellBSSize bs

-- Standard types
-- These need to be in a separate file for TH staging reasons

makeLiftPir ''Bool
makeLiftPir ''Maybe
makeLiftPir ''Either
makeLiftPir ''[]
-- include a few tuple instances for convenience
makeLiftPir ''(,)
makeLiftPir ''(,,)
makeLiftPir ''(,,,)
makeLiftPir ''(,,,,)
