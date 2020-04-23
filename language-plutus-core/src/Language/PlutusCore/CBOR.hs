{-# OPTIONS_GHC -fno-warn-orphans #-}

{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE StandaloneDeriving   #-}
{-# LANGUAGE TypeApplications     #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}

-- | Serialise instances for Plutus Core types. Make sure to read the Note [Stable encoding of PLC]
-- before touching anything in this file.

module Language.PlutusCore.CBOR (serialiseProg, deserialiseProg, deserialiseProgOrFail) where

import           Language.PlutusCore.Core
import           Language.PlutusCore.DeBruijn
import           Language.PlutusCore.Error
import           Language.PlutusCore.Lexer.Type
import           Language.PlutusCore.MkPlc      (TyVarDecl (..), VarDecl (..))
import           Language.PlutusCore.Name
import           Language.PlutusCore.Universe
import           PlutusPrelude

import           Codec.CBOR.Decoding
import           Codec.CBOR.Encoding
import           Codec.Serialise
import           Data.ByteString.Lazy           as BSL
import           Data.Functor.Foldable          hiding (fold)
import           Data.Proxy

{- Note [Stable encoding of PLC]
READ THIS BEFORE TOUCHING ANYTHING IN THIS FILE

We need the encoding of PLC on the blockchain to be *extremely* stable. It *must not* change
arbitrarily, otherwise we'll be unable to read back old transactions and validate them.

Consequently we don't use the derivable instances of `Serialise` for the PLC types that go
on the chain. (Also, the CBOR produced by those instances is more than 60% larger than that
produced by the instances below.)

However, the instances in this file *are* constrained by instances for names, type names,
and annotations. What's to stop the instances for *those* changing, thus changing
the overall encoding on the chain?

The answer is that what goes on the chain is *always* a `Program TyName Name ()`. The instances
for `TyName` and `Name` are nailed down here, and the instance for `()` is standard.

However, having this flexibility allows us to encode e.g. PLC with substantial annotations
(like position information) in situation where the stability is *not* critical, such as
for testing.
-}


{- [Note: Encoding/decoding constructor tags]
   Use `encodeConstructorTag` and `decodeConstructorTag` to encode/decode
   tags representing constructors.  These are just aliases for
   `encodeWord` and `decodeWord`. Note that `encodeWord` is careful about
   sizes and will only use one byte for the tags we have here.  NB: Don't
   use encodeTag or decodeTag; those are for use with a fixed set of CBOR
   tags with predefined meanings which we shouldn't interfere with.
   See http://hackage.haskell.org/package/serialise.
-}
encodeConstructorTag :: Word -> Encoding
encodeConstructorTag = encodeWord

decodeConstructorTag :: Decoder s Word
decodeConstructorTag = decodeWord

-- See Note [The G, the Tag and the Auto].
instance Closed uni => Serialise (Some (TypeIn uni)) where
    encode (Some (TypeIn uni)) = encodeConstructorTag . fromIntegral $ tagOf uni

    decode = go . uniAt . fromIntegral =<< decodeConstructorTag where
        go Nothing    = fail "Failed to decode a universe"
        go (Just uni) = pure uni

-- See Note [The G, the Tag and the Auto].
instance (Closed uni, uni `Everywhere` Serialise) => Serialise (Some (ValueOf uni)) where
    encode (Some (ValueOf uni x)) = encode (Some $ TypeIn uni) <> bring (Proxy @Serialise) uni (encode x)

    decode = go =<< decode where
        go (Some (TypeIn uni)) = Some . ValueOf uni <$> bring (Proxy @Serialise) uni decode

instance Serialise BuiltinName where
    encode bi =
        let i = case bi of
                AddInteger           -> 0
                SubtractInteger      -> 1
                MultiplyInteger      -> 2
                DivideInteger        -> 3
                RemainderInteger     -> 4
                LessThanInteger      -> 5
                LessThanEqInteger    -> 6
                GreaterThanInteger   -> 7
                GreaterThanEqInteger -> 8
                EqInteger            -> 9
                Concatenate          -> 10
                TakeByteString       -> 11
                DropByteString       -> 12
                SHA2                 -> 13
                SHA3                 -> 14
                VerifySignature      -> 15
                EqByteString         -> 16
                QuotientInteger      -> 17
                ModInteger           -> 18
                LtByteString         -> 19
                GtByteString         -> 20
                IfThenElse           -> 21
        in encodeConstructorTag i

    decode = go =<< decodeConstructorTag
        where go 0  = pure AddInteger
              go 1  = pure SubtractInteger
              go 2  = pure MultiplyInteger
              go 3  = pure DivideInteger
              go 4  = pure RemainderInteger
              go 5  = pure LessThanInteger
              go 6  = pure LessThanEqInteger
              go 7  = pure GreaterThanInteger
              go 8  = pure GreaterThanEqInteger
              go 9  = pure EqInteger
              go 10 = pure Concatenate
              go 11 = pure TakeByteString
              go 12 = pure DropByteString
              go 13 = pure SHA2
              go 14 = pure SHA3
              go 15 = pure VerifySignature
              go 16 = pure EqByteString
              go 17 = pure QuotientInteger
              go 18 = pure ModInteger
              go 19 = pure LtByteString
              go 20 = pure GtByteString
              go 21 = pure IfThenElse
              go _  = fail "Failed to decode BuiltinName"

instance Serialise Unique where
    encode (Unique i) = encodeInt i
    decode = Unique <$> decodeInt

instance Serialise Name where
    -- TODO: should we encode the name or not?
    encode (Name txt u) = encode txt <> encode u
    decode = Name <$> decode <*> decode

instance Serialise TyName where
    encode (TyName n) = encode n
    decode = TyName <$> decode

instance Serialise ann => Serialise (Version ann) where
    encode (Version ann n n' n'') = fold [ encode ann, encode n, encode n', encode n'' ]
    decode = Version <$> decode <*> decode <*> decode <*> decode

instance Serialise ann => Serialise (Kind ann) where
    encode = cata a where
        a (TypeF ann)           = encodeConstructorTag 0 <> encode ann
        a (KindArrowF ann k k') = fold [ encodeConstructorTag 1, encode ann, k , k' ]

    decode = go =<< decodeConstructorTag
        where go 0 = Type <$> decode
              go 1 = KindArrow <$> decode <*> decode <*> decode
              go _ = fail "Failed to decode Kind ()"

instance (Closed uni, Serialise ann, Serialise tyname) => Serialise (Type tyname uni ann) where
    encode = cata a where
        a (TyVarF ann tn)        = encodeConstructorTag 0 <> encode ann <> encode tn
        a (TyFunF ann t t')      = encodeConstructorTag 1 <> encode ann <> t <> t'
        a (TyIFixF ann pat arg)  = encodeConstructorTag 2 <> encode ann <> pat <> arg
        a (TyForallF ann tn k t) = encodeConstructorTag 3 <> encode ann <> encode tn <> encode k <> t
        a (TyBuiltinF ann con)   = encodeConstructorTag 4 <> encode ann <> encode con
        a (TyLamF ann n k t)     = encodeConstructorTag 5 <> encode ann <> encode n <> encode k <> t
        a (TyAppF ann t t')      = encodeConstructorTag 6 <> encode ann <> t <> t'

    decode = go =<< decodeConstructorTag
        where go 0 = TyVar <$> decode <*> decode
              go 1 = TyFun <$> decode <*> decode <*> decode
              go 2 = TyIFix <$> decode <*> decode <*> decode
              go 3 = TyForall <$> decode <*> decode <*> decode <*> decode
              go 4 = TyBuiltin <$> decode <*> decode
              go 5 = TyLam <$> decode <*> decode <*> decode <*> decode
              go 6 = TyApp <$> decode <*> decode <*> decode
              go _ = fail "Failed to decode Type TyName ()"

instance Serialise DynamicBuiltinName where
    encode (DynamicBuiltinName name) = encode name
    decode = DynamicBuiltinName <$> decode

instance Serialise ann => Serialise (Builtin ann) where
    encode (BuiltinName ann bn)     = encodeConstructorTag 0 <> encode ann <> encode bn
    encode (DynBuiltinName ann dbn) = encodeConstructorTag 1 <> encode ann <> encode dbn

    decode = go =<< decodeConstructorTag
        where go 0 = BuiltinName <$> decode <*> decode
              go 1 = DynBuiltinName <$> decode <*> decode
              go _ = fail "Failed to decode Builtin ()"

instance ( Closed uni
         , uni `Everywhere` Serialise
         , Serialise ann
         , Serialise tyname
         , Serialise name
         ) => Serialise (Term tyname name uni ann) where
    encode = cata a where
        a (VarF ann n)           = encodeConstructorTag 0 <> encode ann <> encode n
        a (TyAbsF ann tn k t)    = encodeConstructorTag 1 <> encode ann <> encode tn <> encode k <> t
        a (LamAbsF ann n ty t)   = encodeConstructorTag 2 <> encode ann <> encode n <> encode ty <> t
        a (ApplyF ann t t')      = encodeConstructorTag 3 <> encode ann <> t <> t'
        a (ConstantF ann c)      = encodeConstructorTag 4 <> encode ann <> encode c
        a (TyInstF ann t ty)     = encodeConstructorTag 5 <> encode ann <> t <> encode ty
        a (UnwrapF ann t)        = encodeConstructorTag 6 <> encode ann <> t
        a (IWrapF ann pat arg t) = encodeConstructorTag 7 <> encode ann <> encode pat <> encode arg <> t
        a (ErrorF ann ty)        = encodeConstructorTag 8 <> encode ann <> encode ty
        a (BuiltinF ann bi)      = encodeConstructorTag 9 <> encode ann <> encode bi

    decode = go =<< decodeConstructorTag
        where go 0 = Var <$> decode <*> decode
              go 1 = TyAbs <$> decode <*> decode <*> decode <*> decode
              go 2 = LamAbs <$> decode <*> decode <*> decode <*> decode
              go 3 = Apply <$> decode <*> decode <*> decode
              go 4 = Constant <$> decode <*> decode
              go 5 = TyInst <$> decode <*> decode <*> decode
              go 6 = Unwrap <$> decode <*> decode
              go 7 = IWrap <$> decode <*> decode <*> decode <*> decode
              go 8 = Error <$> decode <*> decode
              go 9 = Builtin <$> decode <*> decode
              go _ = fail "Failed to decode Term TyName Name ()"

instance ( Closed uni
         , Serialise ann
         , Serialise tyname
         , Serialise name
         ) => Serialise (VarDecl tyname name uni ann) where
    encode (VarDecl t name tyname ) = encode t <> encode name <> encode tyname
    decode = VarDecl <$> decode <*> decode <*> decode

instance (Serialise ann, Serialise tyname)  => Serialise (TyVarDecl tyname ann) where
    encode (TyVarDecl t tyname kind) = encode t <> encode tyname <> encode kind
    decode = TyVarDecl <$> decode <*> decode <*> decode

instance ( Closed uni
         , uni `Everywhere` Serialise
         , Serialise ann
         , Serialise tyname
         , Serialise name
         ) => Serialise (Program tyname name uni ann) where
    encode (Program ann v t) = encode ann <> encode v <> encode t
    decode = Program <$> decode <*> decode <*> decode

deriving newtype instance (Serialise a) => Serialise (Normalized a)

instance Serialise a => Serialise (Token a)
-- instance Serialise AlexPosn
instance Serialise Keyword
instance Serialise Special

deriving newtype instance Serialise Index

instance Serialise DeBruijn where
    encode (DeBruijn txt i) = encode txt <> encode i
    decode = DeBruijn <$> decode <*> decode

instance Serialise TyDeBruijn where
    encode (TyDeBruijn n) = encode n
    decode = TyDeBruijn <$> decode

instance (Serialise ann) => Serialise (ParseError ann)
instance ( Closed uni
         , uni `Everywhere` Serialise
         , Serialise tyname
         , Serialise name
         , Serialise ann
         ) => Serialise (NormCheckError tyname name uni ann)
instance (Serialise ann) => Serialise (UniqueError ann)
instance Serialise UnknownDynamicBuiltinNameError
instance (Closed uni, uni `Everywhere` Serialise, Serialise ann) => Serialise (InternalTypeError uni ann)
instance (Closed uni, uni `Everywhere` Serialise, Serialise ann) => Serialise (TypeError uni ann)
instance (Closed uni, uni `Everywhere` Serialise, Serialise ann) => Serialise (Error uni ann)


{- Serialising the unit annotation takes up space: () is converted to
   the CBOR `null` value, which is encoded as the byte 0xF6.  In
   typical examples these account for 30% or more of the bytes in a
   serialised PLC program.  We don't actually need to serialise unit
   annotations since we know where they're going to appear when we're
   deserialising, and we know what the value has to be.  The
   `InvisibleUnit` type below has a `Serialise` instance which
   takes care of this for us: `serialise (InvisibleUnit () <$ prog)`
    will serialise a program omitting the unit annotations, and
   `deserialise` will give us back an `InvisibleUnit`-annotated program
   which we can convert back to a ()-annotated program with `() <$ ...`.
   The functions `serialiseProg`, `deserialiseProg` and `deserialiseProgOrFail`
   do the conversions for us, so that the `InvisibleUnit` type doesn't have
   to be exposed to uesrs.  These functions should always be used to serialise
   and deserialise ()-annotated programs.

   A possible problem is that `() <$ prog` has to visit every node in
   the AST, which would incur a cost on chain.  `InvisibleUnit`
   is coercible to `()` at zero cost, and this should extend to the
   entire AST.  The functions below attempt to do this.
-}

newtype InvisibleUnit = InvisibleUnit ()

instance Serialise InvisibleUnit where
    encode = mempty
    decode = pure (InvisibleUnit ())


{- Everything works fine if you just use `<$` to change the annotations, but
   things go wrong when you try to use `coerce`. -}

serialiseProg :: (Closed uni, uni `Everywhere` Serialise) =>
                 Program TyName Name uni () -> BSL.ByteString
serialiseProg p =
    let p1 = fmap (coerce :: () -> InvisibleUnit) p
    in serialise p1

{- You can also delete the type annotation on coerce and replace it with a
   much more unpleasant one on p1.  What I can't get to work is to have

     coerce p

   instead of

     fmap coerce p

   This is annoying because it's presumably actually doing a lot of
   the work that we're trying to avoid with coerce (although I don't
   know that for sure).  This *does* work with a simple expression
   language equipped with annotations, where the compiler knows that
   the representation of an entire ()-annotated AST is the same as the
   representation of the InvisibleUnit-annotated version.  Universes
   seem to complicate matters, but I think there's more to it than
   that because it doesn't work even if you fix uni to be
   DefaultUniverse.
-}

deserialiseProg :: (Closed uni, uni `Everywhere` Serialise) =>
                   BSL.ByteString -> Program TyName Name uni ()
deserialiseProg s =
    let p = deserialise s :: (Closed uni, uni `Everywhere` Serialise) =>
            Program TyName Name uni InvisibleUnit
    in fmap coerce p


deserialiseProgOrFail :: (Closed uni, uni `Everywhere` Serialise) =>
                         BSL.ByteString -> Either DeserialiseFailure (Program TyName Name uni ())
deserialiseProgOrFail s =
    let p = deserialiseOrFail s :: (Closed uni, uni `Everywhere` Serialise) =>
                Either DeserialiseFailure (Program TyName Name uni InvisibleUnit)
    in fmap (fmap coerce) p

{-
deserialiseProg2 :: BSL.ByteString -> Program TyName Name DefaultUni ()
deserialiseProg2 s =
    let p = deserialise s :: Program TyName Name DefaultUni InvisibleUnit
    in coerce p :: Program TyName Name DefaultUni ()

This gives the error:
   Couldn't match type ‘InvisibleUnit’ with ‘()’
        arising from a use of ‘coerce’

I'm finding that rather mysterious.
-}
