{-# LANGUAGE BangPatterns       #-}
{-# LANGUAGE DeriveAnyClass     #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE LambdaCase         #-}
{-# LANGUAGE MultiWayIf         #-}
{-# LANGUAGE OverloadedStrings  #-}
{-# LANGUAGE TypeApplications   #-}
{-# LANGUAGE ViewPatterns       #-}

module PlutusCore.Data (Data (..)) where

import           Codec.CBOR.Decoding       (Decoder)
import qualified Codec.CBOR.Decoding       as CBOR
import           Codec.CBOR.Encoding       (Encoding)
import qualified Codec.CBOR.Encoding       as CBOR
import qualified Codec.CBOR.Magic          as CBOR
import           Codec.Serialise           (Serialise (decode, encode))
import           Codec.Serialise.Decoding  (decodeSequenceLenIndef, decodeSequenceLenN)
import           Control.DeepSeq           (NFData)
import           Control.Monad.Except
import           Data.Bits                 (shiftR)
import qualified Data.ByteString           as BS
import qualified Data.ByteString.Lazy      as BSL
import           Data.Text.Prettyprint.Doc
import           Data.Word                 (Word64, Word8)
import           GHC.Generics
import           Prelude

-- | A generic "data" type.
--
-- The main constructor 'Constr' represents a datatype value in sum-of-products
-- form: @Constr i args@ represents a use of the @i@th constructor along with its arguments.
--
-- The other constructors are various primitives.
data Data =
      Constr Integer [Data]
    | Map [(Data, Data)]
    | List [Data]
    | I Integer
    | B BS.ByteString
    deriving stock (Show, Eq, Ord, Generic)
    deriving anyclass (NFData)

instance Pretty Data where
    pretty = \case
        Constr _ ds -> angles (sep (punctuate comma (fmap pretty ds)))
        Map entries -> braces (sep (punctuate comma (fmap (\(k, v) -> pretty k <> ":" <+> pretty v) entries)))
        List ds     -> brackets (sep (punctuate comma (fmap pretty ds)))
        I i         -> pretty i
        B b         -> viaShow b

{- Note [Encoding via Term]
We want to write a custom encoder/decoder for Data (i.e. not use the Generic version), but actually
doing this is a pain. So instead we go via the CBOR 'Term' representation, which lets us process a
more structured representation, which is a lot easier.
-}

instance Serialise Data where
    -- See Note [Encoding via Term]
    encode = encodeData
    decode = decodeData

{- Note [CBOR alternative tags]
We've proposed to add additional tags to the CBOR standard to cover (essentially) sum types.
This is exactly what we need to encode the 'Constr' constructor of 'Data' in an unambiguous way.

The tags aren't *quite* accepted yet, but they're clearly going to accept so we might as well
start using them.

The scheme is:
- Alternatives 0-6 -> tags 121-127, followed by the arguments in a list
- Alternatives 7-127 -> tags 1280-1400, followed by the arguments in a list
- Any alternatives, including those that don't fit in the above -> tag 102 followed by a list containing
an unsigned integer for the actual alternative, and then the arguments in a (nested!) list.
-}

{- Note [The 64-byte limit]
We impose a 64-byte *on-the-wire* limit on the leaves of a serialized 'Data'. This prevents people from inserting
Mickey Mouse entire.

The simplest way of doing this is to check during deserialization that we never deserialize something that uses
more than 64-bytes, and this is largely what we do. Then it's the user's problem to not produce something too big.

But this is quite inconvenient, so see Note [Evading the 64-byte limit] for how we get around this.
-}

{- Note [Evading the 64-byte limit]
Implementing Note [The 64-byte limit] naively would be quite annoying:
- Users would be responsible for not creating Data values with leaves that were too big.
- If a script *required* such a thing (e.g. a counter that somehow got above 64 bytes), then the user is totally
stuck: the script demands something they cannot represent.

This is unpleasant and introduces limits. Probably limits that nobody will hit, but it's nicer to just not have them.
And it turns out that we can evade the problem with some clever encoding.

The fundamental argument is that an *indefinite-length* CBOR bytestring is just as obfuscated as a list of bytestrings,
since it consists of a list of chunks *with metadata*. Since we already allow people to make lists of <64 byte bytestrings,
we might as well let them make indefinite-length bytestrings too.

So that solves the problem for bytestrings: if they are >64bytes, we encode them as indefinite-length bytestrings
with 64-byte chunks. We have to write our own encoders/decoders so we can produce chunks of the right size and check
the sizes when we decode, but that's okay.

For integers, we have two cases. Small integers (<64bits) can be encoded normally. Big integers are already
encoded *with a byte string*. The spec allows this to be an indefinite-length bytestring (although cborg doesn't
like it), so we can reuse our trick. Again, we need to write some manual encoders/decoders.
-}

-- | Turn Data into a CBOR Term.
encodeData :: Data -> Encoding
encodeData = \case
    -- See Note [CBOR alternative tags]
    Constr i ds | 0 <= i && i < 7   -> CBOR.encodeTag (fromIntegral (121 + i)) <> encode ds
    Constr i ds | 7 <= i && i < 128 -> CBOR.encodeTag (fromIntegral (1280 + (i - 7))) <> encode ds
    Constr i ds | otherwise         ->
                  let tagEncoding = if fromIntegral (minBound @Word64) <= i && i <= fromIntegral (maxBound @Word64)
                                    then CBOR.encodeWord64 (fromIntegral i)
                                    -- This is a "correct"-ish encoding of the tag, but it will *not* deserialise, since we insist on a
                                    -- 'Word64' when we deserialise. So this is really a "soft" failure, without using 'error' or something.
                                    else CBOR.encodeInteger i
                  in CBOR.encodeTag 102 <> CBOR.encodeListLen 2 <> tagEncoding <> encode ds
    Map es                          -> CBOR.encodeMapLen (fromIntegral $ length es) <> mconcat [ encode t <> encode t' | (t, t') <-es ]
    List ds                         -> encode ds
    I i                             -> encodeInteger i
    B b                             -> encodeBs b

-- Logic for choosing encoding borrowed from Codec.CBOR.Write
-- | Given an integer, create a 'CBOR.Term' that encodes it, following our size restrictions.
encodeInteger :: Integer -> Encoding
-- If it fits in a Word64, then it's less than 64 bytes for sure, and we can just send it off
-- as a normal integer for cborg to deal with
encodeInteger i | i >= 0 , i <= fromIntegral (maxBound :: Word64) = CBOR.encodeInteger i
                | i <  0 , i >= -1 - fromIntegral (maxBound :: Word64) = CBOR.encodeInteger i
-- Otherwise, it would be encoded as a bignum anyway, so we manually do the bignum
-- encoding with a bytestring inside, and since we use bsToTerm, that bytestring will
-- get chunked up if it's too big.
-- See Note [Evading the 64-byte limit]
encodeInteger i | i >= 0 = CBOR.encodeTag 2 <> encodeBs (integerToBytes i)
encodeInteger i | otherwise = CBOR.encodeTag 3 <> encodeBs (integerToBytes (-1 -i))

-- Taken exactly from Codec.CBOR.Write
integerToBytes :: Integer -> BS.ByteString
integerToBytes n0
  | n0 == 0   = BS.pack [0]
  | otherwise = BS.pack (reverse (go n0))
  where
    go n | n == 0    = []
         | otherwise = narrow n : go (n `shiftR` 8)

    narrow :: Integer -> Word8
    narrow = fromIntegral

-- | Given an bytestring, create a 'CBOR.Term' that encodes it, following our size restrictions.
encodeBs :: BS.ByteString -> Encoding
encodeBs b | BS.length b <= 64 = CBOR.encodeBytes b
-- It's a bit tricky to get cborg to emit an indefinite-length bytestring with chunks that we control,
-- so we encode it manually
-- See Note [Evading the 64-byte limit]
encodeBs b = CBOR.encodeBytesIndef <> foldMap encode (to64ByteChunks b) <> CBOR.encodeBreak

-- | Turns a 'BS.ByteString' into a list of <=64 byte chunks.
to64ByteChunks :: BS.ByteString -> [BS.ByteString]
to64ByteChunks b | BS.length b > 64 =
                   let (chunk, rest) = BS.splitAt 64 b
                   in chunk:to64ByteChunks rest
to64ByteChunks b = [b]

{- Note [Definite and indefinite forms of CBOR]
CBOR is annoying and you can have both definite (with a fixed length) and indefinite lists, maps, etc.

So we have to be careful to handle both cases when decoding. When encoding we mostly don't make
the indefinite kinds, but see Note [Avoiding the 64-byte limit] for some cases where we do.
-}

-- | Turn a CBOR Term into Data if possible.
decodeData :: Decoder s Data
decodeData = CBOR.peekTokenType >>= \case
  -- These integers are at most 64 *bits*, so certainly less than 64 *bytes*
  CBOR.TypeUInt         -> I <$> CBOR.decodeInteger
  CBOR.TypeUInt64       -> I <$> CBOR.decodeInteger
  CBOR.TypeNInt         -> I <$> CBOR.decodeInteger
  CBOR.TypeNInt64       -> I <$> CBOR.decodeInteger
  -- See Note [The 64-byte limit]
  CBOR.TypeInteger      -> I <$> decodeBoundedBigInteger

  -- See Note [The 64-byte limit]
  CBOR.TypeBytes        -> B <$> decodeBoundedBytes
  CBOR.TypeBytesIndef   -> B . BSL.toStrict <$> decodeBoundedBytesIndef

  CBOR.TypeListLen      -> decodeList
  CBOR.TypeListLen64    -> decodeList
  CBOR.TypeListLenIndef -> decodeList

  CBOR.TypeMapLen       -> decodeMap
  CBOR.TypeMapLen64     -> decodeMap
  CBOR.TypeMapLenIndef  -> decodeMap

  CBOR.TypeTag          -> decodeConstr
  CBOR.TypeTag64        -> decodeConstr

  t                     -> fail ("Unrecognized value of type " ++ show t)

decodeBoundedBigInteger :: Decoder s Integer
decodeBoundedBigInteger = do
    tag <- CBOR.decodeTag
    -- Bignums contain a bytestring as the payload
    bs <- CBOR.peekTokenType >>= \case
        CBOR.TypeBytes      -> decodeBoundedBytes
        CBOR.TypeBytesIndef -> BSL.toStrict <$> decodeBoundedBytesIndef
        t                   -> fail ("Bignum must contain a byte string, got: " ++ show t)
    -- Depending on the tag, the bytestring is either a positive or negative integer
    case tag of
        2 -> pure $ CBOR.uintegerFromBytes bs
        3 -> pure $ CBOR.nintegerFromBytes bs
        t -> fail ("Bignum tag must be one of 2 or 3, got: " ++ show t)

-- Adapted from Codec.CBOR.Read
decodeBoundedBytesIndef :: Decoder s BSL.ByteString
decodeBoundedBytesIndef = CBOR.decodeBytesIndef >> decodeBoundedBytesIndefLen []

-- Adapted from Codec.CBOR.Read, to call the size-checking bytestring decoder
decodeBoundedBytesIndefLen :: [BS.ByteString] -> Decoder s BSL.ByteString
decodeBoundedBytesIndefLen acc = do
    stop <- CBOR.decodeBreakOr
    if stop then return $! BSL.fromChunks (reverse acc)
            else do !bs <- decodeBoundedBytes
                    decodeBoundedBytesIndefLen (bs : acc)

decodeBoundedBytes :: Decoder s BS.ByteString
decodeBoundedBytes =  do
  b <- CBOR.decodeBytes
  -- See Note [The 64-byte limit]
  unless (BS.length b <= 64) $ fail "ByteString exceeds 64 bytes"
  pure b

decodeList :: Decoder s Data
decodeList = List <$> decodeListOf decodeData

decodeListOf :: Decoder s x -> Decoder s [x]
decodeListOf decoder = CBOR.decodeListLenOrIndef >>= \case
  Nothing -> decodeSequenceLenIndef (flip (:)) [] reverse   decoder
  Just n  -> decodeSequenceLenN     (flip (:)) [] reverse n decoder

decodeMap :: Decoder s Data
decodeMap = CBOR.decodeMapLenOrIndef >>= \case
  Nothing -> Map <$> decodeSequenceLenIndef (flip (:)) [] reverse   decodePair
  Just n  -> Map <$> decodeSequenceLenN     (flip (:)) [] reverse n decodePair
  where
  decodePair = (,) <$> decodeData <*> decodeData

-- See note [CBOR alternative tags] for the encoding scheme.
decodeConstr :: Decoder s Data
decodeConstr = CBOR.decodeTag64 >>= \case
  102 -> decodeConstrExtended
  t | 121 <= t && t < 128 ->
         Constr (fromIntegral t - 121) <$> decodeListOf decodeData
  t | 1280 <= t && t < 1401 ->
         Constr ((fromIntegral t - 1280) + 7) <$> decodeListOf decodeData
  t -> fail ("Unrecognized tag " ++ show t)
  where
  decodeConstrExtended = do
    len <- CBOR.decodeListLenOrIndef
    i <- CBOR.decodeWord64
    args <- decodeListOf decodeData
    case len of
      Nothing -> do
        done <- CBOR.decodeBreakOr
        unless done $ fail "Expected exactly two elements"
      Just n -> unless (n == 2) $ fail "Expected exactly two elements"
    pure $ Constr (fromIntegral i) args
