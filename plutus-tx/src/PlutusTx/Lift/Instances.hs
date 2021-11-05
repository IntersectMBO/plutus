{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE DefaultSignatures     #-}
{-# LANGUAGE DeriveAnyClass        #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE PolyKinds             #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE UndecidableInstances  #-}
{-# OPTIONS_GHC -Wno-orphans #-}
module PlutusTx.Lift.Instances () where

import PlutusCore qualified as PLC

import PlutusCore.Data
import PlutusTx.Builtins
import PlutusTx.Builtins.Internal (BuiltinList)
import PlutusTx.Lift.Class


import PlutusIR
import PlutusIR.MkPir

import Data.ByteString qualified as BS
import Data.Kind qualified as GHC
import Data.Proxy
import Data.Text qualified as Text

import GHC.TypeLits (ErrorMessage (..), TypeError)

-- We do not use qualified import because the whole module contains off-chain code
import PlutusTx.Builtins.Class (FromBuiltin)
import Prelude as Haskell

-- Derived instances

-- This instance ensures that we can apply typeable type constructors to typeable arguments and get a typeable
-- type. We need the kind variable, so that partial application of type constructors works.
instance (Typeable uni (f :: * -> k), Typeable uni (a :: *)) => Typeable uni (f a) where
    typeRep _ = TyApp () <$> typeRep (Proxy :: Proxy f) <*> typeRep (Proxy :: Proxy a)

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
instance Typeable uni (->) where
    typeRep _ = do
        a <- PLC.liftQuote $ PLC.freshTyName "a"
        b <- PLC.liftQuote $ PLC.freshTyName "b"
        let tvda = TyVarDecl () a (Type ())
            tvdb = TyVarDecl () b (Type ())
        pure $ mkIterTyLam [tvda, tvdb] $ TyFun () (mkTyVar () tvda) (mkTyVar () tvdb)

-- Primitives

typeRepBuiltin
    :: forall (a :: GHC.Type) uni fun. uni `PLC.Includes` a
    => Proxy a -> RTCompile uni fun (Type TyName uni ())
typeRepBuiltin (_ :: Proxy a) = pure $ mkTyBuiltin @_ @a ()

liftBuiltin
    :: forall a uni fun. uni `PLC.Includes` a
    => a -> RTCompile uni fun (Term TyName Name uni fun ())
liftBuiltin = pure . mkConstant ()

instance (TypeError ('Text "Int is not supported, use Integer instead"))
    => Typeable uni Int where
    typeRep = Haskell.error "unsupported"

instance (TypeError ('Text "Int is not supported, use Integer instead"))
    => Lift uni Int where
    lift = Haskell.error "unsupported"

instance uni `PLC.Includes` Integer => Typeable uni Integer where
    typeRep = typeRepBuiltin

instance uni `PLC.Includes` Integer => Lift uni Integer where
    lift = liftBuiltin

instance uni `PLC.Includes` BS.ByteString => Typeable uni BS.ByteString where
    typeRep = typeRepBuiltin

instance uni `PLC.Includes` BS.ByteString => Lift uni BS.ByteString where
    lift = liftBuiltin

instance uni `PLC.Includes` Data => Typeable uni BuiltinData where
    typeRep _ = typeRepBuiltin (Proxy @Data)

instance uni `PLC.Includes` Data => Lift uni BuiltinData where
    lift d = liftBuiltin (builtinDataToData d)

instance uni `PLC.Includes` BS.ByteString => Typeable uni BuiltinByteString where
    typeRep _proxyPByteString = typeRepBuiltin (Proxy @BS.ByteString)

instance uni `PLC.Includes` BS.ByteString => Lift uni BuiltinByteString where
    lift b = liftBuiltin $ fromBuiltin b

instance uni `PLC.Includes` Text.Text => Typeable uni BuiltinString where
    typeRep _proxyPByteString = typeRepBuiltin (Proxy @Text.Text)

instance uni `PLC.Includes` Text.Text => Lift uni BuiltinString where
    lift b = liftBuiltin $ fromBuiltin b

instance (FromBuiltin arep a, uni `PLC.Includes` [a]) => Lift uni (BuiltinList arep) where
    lift b = liftBuiltin $ fromBuiltin b

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
