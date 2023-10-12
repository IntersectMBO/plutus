-- editorconfig-checker-disable-file
{-# LANGUAGE CPP                   #-}
{-# LANGUAGE ConstraintKinds       #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE DerivingStrategies    #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE PolyKinds             #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE UndecidableInstances  #-}
module PlutusTx.Lift.Class
    ( Typeable (..)
    , Lift (..)
    , RTCompile
    ) where

import PlutusIR
import PlutusIR.Compiler.Definitions

import PlutusCore qualified as PLC
import PlutusCore.Crypto.BLS12_381.G1 (Element)
import PlutusCore.Crypto.BLS12_381.G2 (Element)
import PlutusCore.Crypto.BLS12_381.Pairing (MlResult)
import PlutusCore.Data
import PlutusCore.Quote
import PlutusIR.MkPir
import PlutusTx.Builtins
import PlutusTx.Builtins.Class (FromBuiltin)
import PlutusTx.Builtins.Internal (BuiltinList)

import Language.Haskell.TH qualified as TH hiding (newName)

import Data.ByteString qualified as BS
import Data.Kind qualified as GHC
import Data.Proxy
import Data.Text qualified as T
import GHC.TypeLits (ErrorMessage (..), TypeError)

-- We do not use qualified import because the whole module contains off-chain code
import Prelude as Haskell

{- Note [Compiling at TH time and runtime]
We want to reuse PIR's machinery for defining datatypes. However, one cannot
get a PLC Type consisting of the compiled PIR type, because the compilation of the
definitions is done by making a *term*.

So we use the abstract support for handling definitions in PIR, MonadDefs. Typeable
then has `typeRep :: Proxy a -> RTCompile uni fun (Type TyName uni ())`,
which says that you can get the type in some compilation monad (which
you will later have to discharge yourself).

This means that the TH expressions we are generating are not for `Type`s directly, but rather
for monadic expressions that will, at runtime, compute types. We are effectively generating
a specialized compiler.

We thus have two pieces of compilation going on here:
- At TH time, we reify information about datatypes, and construct specialized compilation expressions
  for the various parts.
- At runtime, we actually run these and create definitions etc.

The interplay between the parts happening at TH time and the parts happening at runtime is somewhat
awkward, but I couldn't think of a better way of doing it.

A particularly awkward feature is that the typeclass constraints required by the code in each
instance are going to be different, and so we can't use reusable functions, instead we need to
inline all the definitions so that the overall expression can have the right constraints inferred.
-}

type RTCompile uni fun = DefT TH.Name uni fun () Quote

-- TODO: try and make this work with type applications
-- | Class for types which have a corresponding Plutus IR type. Instances should always be derived, do not write
-- your own instance!
class Typeable uni (a :: k) where
    -- | Get the Plutus IR type corresponding to this type.
    typeRep :: Proxy a -> RTCompile uni fun (Type TyName uni ())


-- | Class for types which can be lifted into Plutus IR. Instances should be derived, do not write your
-- own instance!
class Lift uni a where
    -- | Get a Plutus IR term corresponding to the given value.
    lift :: a -> RTCompile uni fun (Term TyName Name uni fun ())

-- This instance ensures that we can apply typeable type constructors to typeable arguments and get a typeable
-- type. We need the kind variable, so that partial application of type constructors works.
instance (Typeable uni (f :: GHC.Type -> k), Typeable uni (a :: GHC.Type)) => Typeable uni (f a) where
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
    :: forall (a :: GHC.Type) uni fun. uni `PLC.HasTypeLevel` a
    => Proxy a -> RTCompile uni fun (Type TyName uni ())
typeRepBuiltin (_ :: Proxy a) = pure $ mkTyBuiltin @_ @a ()

liftBuiltin
    :: forall a uni fun. uni `PLC.HasTermLevel` a
    => a -> RTCompile uni fun (Term TyName Name uni fun ())
liftBuiltin = pure . mkConstant ()

instance (TypeError ('Text "Int is not supported, use Integer instead"))
    => Typeable uni Int where
    typeRep = Haskell.error "unsupported"

instance (TypeError ('Text "Int is not supported, use Integer instead"))
    => Lift uni Int where
    lift = Haskell.error "unsupported"

instance uni `PLC.HasTypeLevel` Integer => Typeable uni Integer where
    typeRep = typeRepBuiltin

-- See Note [Lift and Typeable instances for builtins]
instance uni `PLC.HasTermLevel` Integer => Lift uni Integer where
    lift = liftBuiltin

-- See Note [Lift and Typeable instances for builtins]
instance uni `PLC.HasTypeLevel` BS.ByteString => Typeable uni BS.ByteString where
    typeRep = typeRepBuiltin

-- See Note [Lift and Typeable instances for builtins]
instance uni `PLC.HasTermLevel` BS.ByteString => Lift uni BS.ByteString where
    lift = liftBuiltin

-- See Note [Lift and Typeable instances for builtins]
instance uni `PLC.HasTypeLevel` Data => Typeable uni BuiltinData where
    typeRep _ = typeRepBuiltin (Proxy @Data)

-- See Note [Lift and Typeable instances for builtins]
instance uni `PLC.HasTermLevel` Data => Lift uni BuiltinData where
    lift = liftBuiltin . builtinDataToData

-- See Note [Lift and Typeable instances for builtins]
instance uni `PLC.HasTypeLevel` BS.ByteString => Typeable uni BuiltinByteString where
    typeRep _proxyPByteString = typeRepBuiltin (Proxy @BS.ByteString)

-- See Note [Lift and Typeable instances for builtins]
instance uni `PLC.HasTermLevel` BS.ByteString => Lift uni BuiltinByteString where
    lift = liftBuiltin . fromBuiltin

-- See Note [Lift and Typeable instances for builtins]
instance uni `PLC.HasTypeLevel` T.Text => Typeable uni BuiltinString where
    typeRep _proxyPByteString = typeRepBuiltin (Proxy @T.Text)

-- See Note [Lift and Typeable instances for builtins]
instance uni `PLC.HasTermLevel` T.Text => Lift uni BuiltinString where
    lift = liftBuiltin . fromBuiltin

-- See Note [Lift and Typeable instances for builtins]
instance (FromBuiltin arep a, uni `PLC.HasTermLevel` [a]) => Lift uni (BuiltinList arep) where
    lift = liftBuiltin . fromBuiltin

-- See Note [Lift and Typeable instances for builtins]
instance uni `PLC.HasTypeLevel` PlutusCore.Crypto.BLS12_381.G1.Element =>
        Typeable uni BuiltinBLS12_381_G1_Element where
    typeRep _ = typeRepBuiltin (Proxy @PlutusCore.Crypto.BLS12_381.G1.Element)

-- See Note [Lift and Typeable instances for builtins]
instance uni `PLC.HasTermLevel` PlutusCore.Crypto.BLS12_381.G1.Element =>
        Lift uni BuiltinBLS12_381_G1_Element where
    lift = liftBuiltin . fromBuiltin

-- See Note [Lift and Typeable instances for builtins]
instance uni `PLC.HasTypeLevel` PlutusCore.Crypto.BLS12_381.G2.Element =>
        Typeable uni BuiltinBLS12_381_G2_Element where
    typeRep _ = typeRepBuiltin (Proxy @PlutusCore.Crypto.BLS12_381.G2.Element)

-- See Note [Lift and Typeable instances for builtins]
instance uni `PLC.HasTermLevel` PlutusCore.Crypto.BLS12_381.G2.Element =>
        Lift uni BuiltinBLS12_381_G2_Element where
    lift = liftBuiltin . fromBuiltin

-- See Note [Lift and Typeable instances for builtins]
instance uni `PLC.HasTypeLevel` PlutusCore.Crypto.BLS12_381.Pairing.MlResult =>
        Typeable uni BuiltinBLS12_381_MlResult where
    typeRep _ = typeRepBuiltin (Proxy @PlutusCore.Crypto.BLS12_381.Pairing.MlResult)

-- See Note [Lift and Typeable instances for builtins]
instance uni `PLC.HasTermLevel` PlutusCore.Crypto.BLS12_381.Pairing.MlResult =>
        Lift uni BuiltinBLS12_381_MlResult where
    lift = liftBuiltin . fromBuiltin

{- Note [Lift and Typeable instances for builtins]
We can, generally, lift builtin values. We just make a constant with the value inside.
However, in Plutus Tx we use opaque types for most builtin types to avoid people
trying to pattern match on them. So the types don't quite match up with what we need
to put inside the constant.

Fortunately, we have To/FromBuiltin, which happen to do what we want.
See Note [Builtin types and their Haskell versions].
This is arguably slightly an abuse: the versions of the types that we want in
Plutus Tx source code and the versions that we use as the implementations of
the builtin types in the universe could be different. But in practice they
aren't. So we can write fairly straightforward instances for most types.

Similarly, for Typeable we may have to use a different type from the opaque one.
-}
