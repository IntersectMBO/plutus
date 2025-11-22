-- editorconfig-checker-disable-file
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

module UntypedPlutusCore.Core.Instance.Flat where

import PlutusCore.Pretty
import PlutusCore.Version qualified as PLC
import PlutusPrelude
import UntypedPlutusCore.Core.Instance.Pretty ()
import UntypedPlutusCore.Core.Type

import Control.Lens
import Control.Monad
import Data.Vector qualified as V
import PlutusCore.Flat
import PlutusCore.Flat.Decoder
import PlutusCore.Flat.Encoder
import PlutusCore.Flat.Encoder.Strict (sizeListWith)
import PlutusCore.FlatInstances
import Universe

{-
The definitions in this file rely on some Flat instances defined for typed plutus core.
You can find those in PlutusCore.Flat.
-}

{- Note [Stable encoding of UPLC]
READ THIS BEFORE TOUCHING ANYTHING IN THIS FILE

We need the encoding of PLC on the blockchain to be *extremely* stable. It *must not* change
arbitrarily, otherwise we'll be unable to read back old transactions and validate them.

Consequently we don't use the derivable instances of `Flat` for the PLC types that go
on the chain.

However, the instances in this file *are* constrained by instances for names, type names,
and annotations. What's to stop the instances for *those* changing, thus changing
the overall encoding on the chain?

The answer is that what goes on the chain is *always* a `Program TyName Name ()`. The instances
for `TyName` and `Name` are nailed down here, and the instance for `()` is standard.

However, having this flexibility allows us to encode e.g. PLC with substantial annotations
(like position information) in situation where the stability is *not* critical, such as
for testing.
-}

{- Note [Encoding/decoding UPLC constructor tags using Flat]
Flat saves space when compared to CBOR by allowing tags to use the minimum
number of bits required for their encoding.

This requires specialised encode/decode functions for each constructor
that encodes a different number of possibilities. Here is a list of the
tags and their used/available encoding possibilities.

\** The BELOW table is for UPLC. **

\| Data type        | Function          | Bit Width | Total | Used | Remaining |
\|------------------|-------------------|-----------|-------|------|-----------|
\| default builtins | encodeBuiltin     | 7         | 128   | 54   | 74        |
\| Terms            | encodeTerm        | 4         | 16    | 10   | 6         |

For format stability we are manually assigning the tag values to the
constructors (and we do not use a generic algorithm that may change this order).

All encodings use the function `safeEncodeBits :: NumBits -> Word8 -> Encoding`, which encodes
at most 8 bits of data, and the first argument specifies how many bits from the 8
available are actually used. This function also checks the size of the `Word8`
argument at runtime.

Flat uses an extra function in its class definition called `size`. Since we want
to reserve some space for future data constructors and we don't want to have the
sizes desynchronised from the encoding and decoding functions we have manual
implementations for them (if they have any constructors reserved for future use).

By default, Flat does not use any space to serialise `()`.
-}

{- Note [Deserialization size limits]
In order to prevent people encoding copyright or otherwise illegal data on the chain, we would like to
restrict the amount of data that can be controlled in an unrestricted fashion by the user. Fortunately,
most of the encoding does no allow much leeway for a user to control its content (when accounting for the
structure of the format itself). The main thing to worry about is bytestrings, but even there, the flat
encoding of bytestrings is a sequence of 255-byte chunks. This is okay, since user-controlled data will
be broken up by the chunk metadata.
-}

-- | Using 4 bits to encode term tags.
termTagWidth :: NumBits
termTagWidth = 4

encodeTermTag :: Word8 -> Encoding
encodeTermTag = safeEncodeBits termTagWidth

decodeTermTag :: Get Word8
decodeTermTag = dBEBits8 termTagWidth

encodeTerm
  :: forall name uni fun ann
   . ( Closed uni
     , uni `Everywhere` Flat
     , Flat fun
     , Flat ann
     , Flat name
     , Flat (Binder name)
     )
  => Term name uni fun ann
  -> Encoding
encodeTerm = \case
  Var ann n -> encodeTermTag 0 <> encode ann <> encode n
  Delay ann t -> encodeTermTag 1 <> encode ann <> encodeTerm t
  LamAbs ann n t -> encodeTermTag 2 <> encode ann <> encode (Binder n) <> encodeTerm t
  Apply ann t t' -> encodeTermTag 3 <> encode ann <> encodeTerm t <> encodeTerm t'
  Constant ann c -> encodeTermTag 4 <> encode ann <> encode c
  Force ann t -> encodeTermTag 5 <> encode ann <> encodeTerm t
  Error ann -> encodeTermTag 6 <> encode ann
  Builtin ann bn -> encodeTermTag 7 <> encode ann <> encode bn
  Constr ann i es -> encodeTermTag 8 <> encode ann <> encode i <> encodeListWith encodeTerm es
  Case ann arg cs -> encodeTermTag 9 <> encode ann <> encodeTerm arg <> encodeListWith encodeTerm (V.toList cs)

decodeTerm
  :: forall name uni fun ann
   . ( Closed uni
     , uni `Everywhere` Flat
     , Flat fun
     , Flat ann
     , Flat name
     , Flat (Binder name)
     )
  => Version
  -> (fun -> Maybe String)
  -> Get (Term name uni fun ann)
decodeTerm version builtinPred = go
  where
    go = handleTerm =<< decodeTermTag
    handleTerm 0 = Var <$> decode <*> decode
    handleTerm 1 = Delay <$> decode <*> go
    handleTerm 2 = LamAbs <$> decode <*> (unBinder <$> decode) <*> go
    handleTerm 3 = Apply <$> decode <*> go <*> go
    handleTerm 4 = Constant <$> decode <*> decode
    handleTerm 5 = Force <$> decode <*> go
    handleTerm 6 = Error <$> decode
    handleTerm 7 = do
      ann <- decode
      fun <- decode
      let t :: Term name uni fun ann
          t = Builtin ann fun
      case builtinPred fun of
        Nothing -> pure t
        Just e -> fail e
    handleTerm 8 = do
      unless (version >= PLC.plcVersion110) $ fail $ "'constr' is not allowed before version 1.1.0, this program has version: " ++ (show $ pretty version)
      Constr <$> decode <*> decode <*> decodeListWith go
    handleTerm 9 = do
      unless (version >= PLC.plcVersion110) $ fail $ "'case' is not allowed before version 1.1.0, this program has version: " ++ (show $ pretty version)
      Case <$> decode <*> go <*> (V.fromList <$> decodeListWith go)
    handleTerm t = fail $ "Unknown term constructor tag: " ++ show t

sizeTerm
  :: forall name uni fun ann
   . ( Closed uni
     , uni `Everywhere` Flat
     , Flat fun
     , Flat ann
     , Flat name
     , Flat (Binder name)
     )
  => Term name uni fun ann
  -> NumBits
  -> NumBits
sizeTerm tm sz =
  let
    sz' = termTagWidth + sz
   in
    case tm of
      Var ann n -> size ann $ size n sz'
      Delay ann t -> size ann $ sizeTerm t sz'
      LamAbs ann n t -> size ann $ size n $ sizeTerm t sz'
      Apply ann t t' -> size ann $ sizeTerm t $ sizeTerm t' sz'
      Constant ann c -> size ann $ size c sz'
      Force ann t -> size ann $ sizeTerm t sz'
      Error ann -> size ann sz'
      Builtin ann bn -> size ann $ size bn sz'
      Constr ann i es -> size ann $ size i $ sizeListWith sizeTerm es sz'
      Case ann arg cs -> size ann $ sizeTerm arg $ sizeListWith sizeTerm (V.toList cs) sz'

{-| An encoder for programs.

It is not easy to use this correctly with @flat@. The simplest thing
is to go via the instance for 'UnrestrictedProgram', which uses this -}
encodeProgram
  :: forall name uni fun ann
   . ( Closed uni
     , uni `Everywhere` Flat
     , Flat fun
     , Flat ann
     , Flat name
     , Flat (Binder name)
     )
  => Program name uni fun ann
  -> Encoding
encodeProgram (Program ann v t) = encode ann <> encode v <> encodeTerm t

decodeProgram
  :: forall name uni fun ann
   . ( Closed uni
     , uni `Everywhere` Flat
     , Flat fun
     , Flat ann
     , Flat name
     , Flat (Binder name)
     )
  => (fun -> Maybe String)
  -> Get (Program name uni fun ann)
decodeProgram builtinPred = do
  ann <- decode
  v <- decode
  Program ann v <$> decodeTerm v builtinPred

sizeProgram
  :: forall name uni fun ann
   . ( Closed uni
     , uni `Everywhere` Flat
     , Flat fun
     , Flat ann
     , Flat name
     , Flat (Binder name)
     )
  => Program name uni fun ann
  -> NumBits
  -> NumBits
sizeProgram (Program ann v t) sz = size ann $ size v $ sizeTerm t sz

{-| A program that can be serialized without any restrictions, e.g.
on the set of allowable builtins or term constructs. It is generally
safe to use this newtype for serializing, but it should only be used
for deserializing in tests. -}
newtype UnrestrictedProgram name uni fun ann = UnrestrictedProgram {unUnrestrictedProgram :: Program name uni fun ann}
  deriving newtype (Functor)

makeWrapped ''UnrestrictedProgram

deriving newtype instance
  (Show name, GShow uni, Everywhere uni Show, Show fun, Show ann, Closed uni)
  => Show (UnrestrictedProgram name uni fun ann)

deriving via
  PrettyAny (UnrestrictedProgram name uni fun ann)
  instance
    DefaultPrettyPlcStrategy (UnrestrictedProgram name uni fun ann)
    => PrettyBy PrettyConfigPlc (UnrestrictedProgram name uni fun ann)

deriving newtype instance
  (PrettyClassic name, PrettyUni uni, Pretty fun, Pretty ann)
  => PrettyBy (PrettyConfigClassic PrettyConfigName) (UnrestrictedProgram name uni fun ann)

deriving newtype instance
  (PrettyReadable name, PrettyUni uni, Pretty fun)
  => PrettyBy (PrettyConfigReadable PrettyConfigName) (UnrestrictedProgram name uni fun ann)

-- This instance does _not_ check for allowable builtins
instance
  ( Closed uni
  , uni `Everywhere` Flat
  , Flat fun
  , Flat ann
  , Flat name
  , Flat (Binder name)
  )
  => Flat (UnrestrictedProgram name uni fun ann)
  where
  encode (UnrestrictedProgram p) = encodeProgram p
  decode = UnrestrictedProgram <$> decodeProgram (const Nothing)

  size (UnrestrictedProgram p) = sizeProgram p
