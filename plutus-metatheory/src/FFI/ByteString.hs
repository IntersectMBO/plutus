{-# LANGUAGE GADTs #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ViewPatterns #-}

{-| The runtime representation of the Agda bytes and bytestrings defined in
@Builtin.ByteString.Byte@ and @Builtin.ByteString.Base@, and
conversions to and from Haskell bytestrings.

The bytestring builtins are implemented in Agda, and the compiled code runs
those implementations on this representation (a list of bytes, each eight
bits). Haskell bytestrings are only used at the boundaries: by the builtins
that are still postulated (hashes, signatures, encoding, serialisation, BLS,
Value), by costing, inside 'Data', and in the constants of the terms that are
passed between Haskell and Agda. -}
module FFI.ByteString
  ( Byte (..)
  , ByteString (..)
  , toHS
  , fromHS
  , pattern BData
  , pattern AgdaTagBS
  , pattern AgdaTagCon
  ) where

import Data.Bits (testBit)
import Data.ByteString qualified as BS
import Data.Type.Equality ((:~:) (Refl))
import Data.Word (Word8)
import PlutusCore.Data (Data (..))
import PlutusCore.Default
  ( DefaultUni (..)
  , Esc
  , Some (..)
  , ValueOf (..)
  , pattern DefaultUniArray
  , pattern DefaultUniList
  , pattern DefaultUniPair
  )
import Unsafe.Coerce (unsafeCoerce)

-- | Agda's @Byte@; the first field is the most significant bit.
data Byte = Byte Bool Bool Bool Bool Bool Bool Bool Bool
  deriving stock (Eq, Show)

-- | Agda's @ByteString@.
data ByteString = BSNil | BSCons Byte ByteString
  deriving stock (Eq, Show)

byteToWord8 :: Byte -> Word8
byteToWord8 (Byte b1 b2 b3 b4 b5 b6 b7 b8) =
  foldl (\acc b -> 2 * acc + if b then 1 else 0) 0 [b1, b2, b3, b4, b5, b6, b7, b8]

word8ToByte :: Word8 -> Byte
word8ToByte w = Byte (t 7) (t 6) (t 5) (t 4) (t 3) (t 2) (t 1) (t 0)
  where
    t = testBit w

toHS :: ByteString -> BS.ByteString
toHS = BS.pack . go
  where
    go BSNil = []
    go (BSCons b bs) = byteToWord8 b : go bs

fromHS :: BS.ByteString -> ByteString
fromHS = BS.foldr (BSCons . word8ToByte) BSNil

{-| Agda's @bDATA@. At runtime @DATA@ is Haskell's 'Data', which holds a Haskell
bytestring; this converts it to and from the Agda representation. -}
pattern BData :: ByteString -> Data
pattern BData bs <- B (fromHS -> bs)
  where
    BData bs = B (toHS bs)

{-# COMPLETE Constr, Map, List, I, BData #-}

{-| Agda's @bytestring@ tag. At runtime it is 'DefaultUniByteString', but its
type is indexed by the Agda representation, since that is the type of the
payload Agda sees in a constant (see 'AgdaTagCon'). -}
pattern AgdaTagBS :: () => a ~ Esc ByteString => DefaultUni a
pattern AgdaTagBS <- (isTagBS -> Just Refl)
  where
    AgdaTagBS = unsafeCoerce DefaultUniByteString

isTagBS :: DefaultUni a -> Maybe (a :~: Esc ByteString)
isTagBS DefaultUniByteString = Just (unsafeCoerce Refl)
isTagBS _ = Nothing

{-| Agda's @tagCon@. At runtime a constant is Haskell's @Some (ValueOf
DefaultUni)@ holding Haskell bytestrings, so that the Haskell side (parsing,
printing, comparing results) can use it directly. Matching on this pattern
converts the bytestrings in the constant (also inside lists, pairs and arrays)
to the Agda representation, and constructing with it converts them back.

The payload seen through this pattern has the Agda representation although its
Haskell type says otherwise. That is fine for the code generated from Agda,
which coerces everything anyway, but such a payload must never be handed to
Haskell code. -}
pattern AgdaTagCon :: () => DefaultUni (Esc a) -> a -> Some (ValueOf DefaultUni)
pattern AgdaTagCon t x <- (toAgdaConstant -> Some (ValueOf t x))
  where
    AgdaTagCon t x = Some (ValueOf t (fromAgdaValue t x))

{-# COMPLETE AgdaTagCon #-}

toAgdaConstant :: Some (ValueOf DefaultUni) -> Some (ValueOf DefaultUni)
toAgdaConstant (Some (ValueOf t x)) = Some (ValueOf t (toAgdaValue t x))

toAgdaValue :: DefaultUni (Esc a) -> a -> a
toAgdaValue DefaultUniByteString x = unsafeCoerce (fromHS x)
toAgdaValue (DefaultUniList t) xs = map (toAgdaValue t) xs
toAgdaValue (DefaultUniPair ta tb) (x, y) = (toAgdaValue ta x, toAgdaValue tb y)
toAgdaValue (DefaultUniArray t) xs = fmap (toAgdaValue t) xs
toAgdaValue _ x = x

fromAgdaValue :: DefaultUni (Esc a) -> a -> a
fromAgdaValue DefaultUniByteString x = toHS (unsafeCoerce x)
fromAgdaValue (DefaultUniList t) xs = map (fromAgdaValue t) xs
fromAgdaValue (DefaultUniPair ta tb) (x, y) = (fromAgdaValue ta x, fromAgdaValue tb y)
fromAgdaValue (DefaultUniArray t) xs = fmap (fromAgdaValue t) xs
fromAgdaValue _ x = x
