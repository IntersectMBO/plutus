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
            I i -> Serialise.encode i
            B b -> Serialise.encode b
            Map entries ->
                CBOR.encodeMapLenIndef
                    <> mconcat [ encodeData k <> encodeData v | (k, v) <- entries ]
                    <> CBOR.encodeBreak
            List ts -> Serialise.encode ts
            Constr i entries -> Serialise.encode i <> Serialise.encode entries

decodeData :: Decoder s Data
decodeData = do
    constr <- CBOR.decodeBool
    if constr
        then Constr <$> Serialise.decode <*> Serialise.decode
        else do
            tkty <- CBOR.peekTokenType
            case tkty of
                CBOR.TypeUInt -> I <$> Serialise.decode
                CBOR.TypeUInt64 -> I <$> Serialise.decode
                CBOR.TypeNInt   -> I <$> Serialise.decode
                CBOR.TypeNInt64 -> I <$> Serialise.decode
                CBOR.TypeInteger -> I <$> Serialise.decode
                CBOR.TypeBytes -> B <$> Serialise.decode
                CBOR.TypeMapLenIndef -> do
                    CBOR.decodeMapLenIndef
                    Map <$> decodeMapIndefLen []
                CBOR.TypeMapLen -> Map <$> Serialise.decode
                CBOR.TypeListLenIndef -> List <$> Serialise.decode
                CBOR.TypeListLen -> List <$> Serialise.decode
                _ -> fail "Invalid encoding"

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
