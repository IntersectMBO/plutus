{-# OPTIONS_GHC -fno-warn-orphans #-}

{-# LANGUAGE LambdaCase           #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}

module Language.UntypedPlutusCore.Core.Instance.CBOR where

import           Language.UntypedPlutusCore.Core.Type

import           Language.PlutusCore.CBOR
import           Language.PlutusCore.Universe

import           Codec.Serialise

import qualified Data.ByteString.Lazy                 as BSL

instance ( Closed uni
         , uni `Everywhere` Serialise
         , Serialise ann
         , Serialise fun
         , Serialise name
         ) => Serialise (Term name uni fun ann) where
    encode = \case
        Var      ann n    -> encodeConstructorTag 0 <> encode ann <> encode n
        Delay    ann t    -> encodeConstructorTag 1 <> encode ann <> encode t
        LamAbs   ann n t  -> encodeConstructorTag 2 <> encode ann <> encode n <> encode t
        Apply    ann t t' -> encodeConstructorTag 3 <> encode ann <> encode t <> encode t'
        Constant ann c    -> encodeConstructorTag 4 <> encode ann <> encode c
        Force    ann t    -> encodeConstructorTag 5 <> encode ann <> encode t
        Error    ann      -> encodeConstructorTag 6 <> encode ann
        Builtin  ann bn   -> encodeConstructorTag 7 <> encode ann <> encode bn

    decode = go =<< decodeConstructorTag
        where go 0 = Var      <$> decode <*> decode
              go 1 = Delay    <$> decode <*> decode
              go 2 = LamAbs   <$> decode <*> decode <*> decode
              go 3 = Apply    <$> decode <*> decode <*> decode
              go 4 = Constant <$> decode <*> decode
              go 5 = Force    <$> decode <*> decode
              go 6 = Error    <$> decode
              go 7 = Builtin  <$> decode <*> decode
              go _ = fail "Failed to decode Term TyName Name ()"

instance ( Closed uni
         , uni `Everywhere` Serialise
         , Serialise ann
         , Serialise fun
         , Serialise name
         ) => Serialise (Program name uni fun ann) where
    encode (Program ann v t) = encode ann <> encode v <> encode t
    decode = Program <$> decode <*> decode <*> decode

{- Note [Serialising unit annotations]

Serialising the unit annotation takes up space: () is converted to the
CBOR `null` value, which is encoded as the byte 0xF6.  In typical
examples these account for 30% or more of the bytes in a serialised
PLC program.  We don't actually need to serialise unit annotations
since we know where they're going to appear when we're deserialising,
and we know what the value has to be.  The `InvisibleUnit` type below
has instances which takes care of this for us: if we have an
`InvisibleUnit`-annotated program `prog` then `serialise prog` will
serialise a program omitting the annotations, and `deserialise` (with
an appropriate type ascription) will give us back an
`InvisibleUnit`-annotated program.

We usually deal with ()-annotated ASTs, so the annotations have to be
converted to and from `InvisibleUnit` if we wish to save space.  The
obvious way to do this is to use `InvisibleUnit <$ ...` and
`() <$ ...`, but these have the disadvantage that they have to traverse the
entire AST and visit every annotation, adding an extra cost which may
be undesirable when deserialising things on-chain.  However,
`InvisibleUnit` has the same underlying representation as `()`, and
we can exploit this using Data.Coerce.coerce to convert entire ASTs
with no run-time overhead.
-}

newtype InvisibleUnit = InvisibleUnit ()

instance Serialise InvisibleUnit where
    encode = mempty
    decode = pure (InvisibleUnit ())

{- Note [Serialising Scripts]

At first sight, all we need to do to serialise a script without unit
annotations appearing in the CBOR is to coerce from `()` to
`InvisibleUnit` and then apply `serialise` as normal.  However, this
isn't sufficient for the ledger code. There are a number of places in
Ledger.Scripts and elsewhere where hashes of objects (`Tx`, for
example) are calculated by serialising the entire object and
calculating a hash, and these objects can contain Scripts themselves.
Serialisation is achieved using the Generic instance of `Serialise`,
which will just use `encode` on everything, including unit
annotations.  we could overcome this by writing explicit `Serialise`
instances for everything.  This would be more space-efficient than the
Generic encoding, but would introduce a lot of extra code.  Instead,
we provide a wrapper class with an instance which performs the
coercions for us.  This is used in `Ledger.Scripts.Script` to
derive a suitable instance of `Serialise` for scripts. -}

newtype OmitUnitAnnotations name uni fun = OmitUnitAnnotations { restoreUnitAnnotations :: Program name uni fun () }
    deriving Serialise via Program name uni fun InvisibleUnit

{-| Convenience functions for serialisation/deserialisation without units -}
serialiseOmittingUnits :: (Closed uni, Serialise name, uni `Everywhere` Serialise, Serialise fun) => Program name uni fun () -> BSL.ByteString
serialiseOmittingUnits = serialise . OmitUnitAnnotations

deserialiseRestoringUnits :: (Closed uni, Serialise name, uni `Everywhere` Serialise, Serialise fun) => BSL.ByteString -> Program name uni fun ()
deserialiseRestoringUnits = restoreUnitAnnotations <$> deserialise

deserialiseRestoringUnitsOrFail :: (Closed uni, Serialise name, uni `Everywhere` Serialise, Serialise fun) =>
                        BSL.ByteString -> Either DeserialiseFailure (Program name uni fun ())
deserialiseRestoringUnitsOrFail bs = restoreUnitAnnotations <$> deserialiseOrFail bs
