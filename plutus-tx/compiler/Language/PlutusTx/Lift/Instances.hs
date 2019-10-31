{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PolyKinds         #-}
{-# LANGUAGE TemplateHaskell   #-}
{-# LANGUAGE TypeApplications  #-}
{-# OPTIONS_GHC -Wno-orphans #-}
module Language.PlutusTx.Lift.Instances () where

import qualified Language.PlutusCore          as PLC

import           Language.PlutusTx.Builtins
import           Language.PlutusTx.Lift.Class

import           Language.PlutusIR
import           Language.PlutusIR.MkPir

import           Data.Proxy

-- Derived instances

-- This instance ensures that we can apply typeable type constructors to typeable arguments and get a typeable
-- type. We need the kind variable, so that partial application of type constructors works.
instance (Typeable (f :: * -> k), Typeable (a :: *)) => Typeable (f a) where
    typeRep _ = TyApp () <$> typeRep (undefined :: Proxy f) <*> typeRep (undefined :: Proxy a)

{- Note [Typeable instances for function types]
Surely there is an obvious 'Typeable' instance for 'a -> b': we just turn it directly
into a 'TyFun'!

However, if you write this instance, you find that it overlaps with the instance for applied
type constructors. For is not '(->) a' an applied type constructor?

Vexing. However, if we run with this, we can define a 'Typeable' instance for '(->)' directly.
What is this? Well, it's something like '\a b . a -> b' as a type function. Which is a rather
silly thing to write, but it does work.
-}
-- See Note [Typeable instances for function types]
instance Typeable (->) where
    typeRep _ = do
        a <- PLC.liftQuote $ PLC.freshTyName () "a"
        b <- PLC.liftQuote $ PLC.freshTyName () "b"
        let tvda = TyVarDecl () a (Type ())
            tvdb = TyVarDecl () b (Type ())
        pure $ mkIterTyLam [tvda, tvdb] $ TyFun () (mkTyVar () tvda) (mkTyVar () tvdb)

-- Primitives

instance Typeable Integer where
    typeRep _ = pure $ TyBuiltin () PLC.TyInteger

instance Lift Integer where
    lift i = pure $ Constant () $ PLC.BuiltinInt () i

instance Typeable ByteString where
    typeRep _ = pure $ TyBuiltin () PLC.TyByteString

instance Lift ByteString where
    lift bs = pure $ Constant () $ PLC.BuiltinBS () bs

-- Standard types
-- These need to be in a separate file for TH staging reasons

makeLift ''Data
makeLift ''Bool
makeLift ''Maybe
makeLift ''Either
makeLift ''[]
makeLift ''()
-- include a few tuple instances for convenience
makeLift ''(,)
makeLift ''(,,)
makeLift ''(,,,)
makeLift ''(,,,,)
