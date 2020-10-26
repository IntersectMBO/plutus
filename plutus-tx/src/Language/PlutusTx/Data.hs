{-# LANGUAGE BangPatterns       #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE LambdaCase         #-}
{-# LANGUAGE OverloadedStrings  #-}
{-# LANGUAGE ViewPatterns       #-}
module Language.PlutusTx.Data (Data (..)) where

import           Prelude                   hiding (fail)

import           Control.Monad.Fail
import qualified Data.ByteString           as BS

import           Codec.CBOR.Decoding       (Decoder)
import qualified Codec.CBOR.Decoding       as CBOR
import           Codec.CBOR.Encoding       (Encoding)
import qualified Codec.CBOR.Encoding       as CBOR
import qualified Codec.Serialise           as Serialise

import           Data.Text.Prettyprint.Doc

import           GHC.Generics

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

instance Pretty Data where
    pretty = \case
        Constr _ ds -> angles (sep (punctuate comma (fmap pretty ds)))
        Map entries -> braces (sep (punctuate comma (fmap (\(k, v) -> pretty k <> ":" <+> pretty v) entries)))
        List ds -> brackets (sep (punctuate comma (fmap pretty ds)))
        I i -> pretty i
        B b -> viaShow b

{- Note [Permissive decoding]
We're using a canonical representation of lists, maps, bytes, and integers. However,
the CBOR library does not guarantee that a TInteger gets encoded as a big integer,
so we can't rely on getting back our canonical version when we decode (see
https://github.com/well-typed/cborg/issues/222). So we need to be permissive
when we decode.
-}

{- Note [Encoding of Data]

All constructors of 'Data' map directly to CBOR primitives, *except* for the
'Constr' constructor. So to encode a 'Data' value we first write a 'Bool'
indicating whether the value is a 'Constr' or something else.

When decoding 'Data', if the leading bit is true we know that we are looking at
a 'Constr', so we can read the two arguments. If it is something else, we
look at the CBOR token type.

-}

-- | Check whether this is using the 'Constr' constructor
isConstr :: Data -> Bool
isConstr = \case
    Constr _ _ -> True
    _ -> False

encodeData :: Data -> Encoding
encodeData dt = CBOR.encodeBool (isConstr dt) <> encodeRest where
    encodeRest = case dt of
            I i -> CBOR.encodeInteger i
            B b -> CBOR.encodeBytes b
            Map entries ->
                CBOR.encodeMapLenIndef
                    <> mconcat [ encodeData k <> encodeData v | (k, v) <- entries ]
                    <> CBOR.encodeBreak
            List ts ->
                CBOR.encodeListLenIndef
                    <> mconcat (encodeData <$> ts)
                    <> CBOR.encodeBreak
            Constr i entries ->
                CBOR.encodeInteger i
                    <> CBOR.encodeListLenIndef
                    <> mconcat (encodeData <$> entries)
                    <> CBOR.encodeBreak

decodeData :: Decoder s Data
decodeData = do
    constr <- CBOR.decodeBool
    if constr
        then do
            !x <- CBOR.decodeInteger
            !y <- do
                CBOR.decodeListLenIndef
                decodeListIndefLen []
            pure $ Constr x y
        else do
            tkty <- CBOR.peekTokenType
            case tkty of
                CBOR.TypeUInt -> do
                    w <- CBOR.decodeWord
                    return $! I $! fromIntegral w
                CBOR.TypeUInt64 -> do
                    w <- CBOR.decodeWord64
                    return $! I $! fromIntegral w
                CBOR.TypeNInt   -> do
                    w <- CBOR.decodeNegWord
                    return $! I $! (-1 - fromIntegral w)
                CBOR.TypeNInt64 -> do
                    w <- CBOR.decodeNegWord64
                    return $! I $! (-1 - fromIntegral w)
                CBOR.TypeInteger -> do
                    !x <- CBOR.decodeInteger
                    return (I x)
                CBOR.TypeBytes -> do
                    !x <- CBOR.decodeBytes
                    return (B x)
                CBOR.TypeMapLenIndef -> do
                    CBOR.decodeMapLenIndef
                    Map <$> decodeMapIndefLen []
                CBOR.TypeListLenIndef -> do
                    CBOR.decodeListLenIndef
                    List <$> decodeListIndefLen []
                _ -> fail "Invalid encoding"

-- from https://hackage.haskell.org/package/cborg-0.2.4.0/docs/src/Codec.CBOR.Term.html#decodeListIndefLen
decodeListIndefLen :: [Data] -> Decoder s [Data]
decodeListIndefLen acc = do
    stop <- CBOR.decodeBreakOr
    if stop then return $ reverse acc
            else do !tm <- decodeData
                    decodeListIndefLen (tm : acc)

-- from https://hackage.haskell.org/package/cborg-0.2.4.0/docs/src/Codec.CBOR.Term.html#decodeMapIndefLen
decodeMapIndefLen :: [(Data, Data)] -> Decoder s [(Data, Data)]
decodeMapIndefLen acc = do
    stop <- CBOR.decodeBreakOr
    if stop then return $ reverse acc
            else do !tm  <- decodeData
                    !tm' <- decodeData
                    decodeMapIndefLen ((tm, tm') : acc)

instance Serialise.Serialise Data where
    encode = encodeData
    decode = decodeData
