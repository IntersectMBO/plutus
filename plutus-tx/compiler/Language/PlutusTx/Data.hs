{-# LANGUAGE LambdaCase #-}
module Language.PlutusTx.Data where

import           Prelude              hiding (fail)

import           Data.Bifunctor       (bimap)
import           Data.Bitraversable   (bitraverse)
import           Data.ByteString.Lazy as BSL

import           Control.Monad.Fail

import qualified Codec.CBOR.Term      as CBOR
import qualified Codec.Serialise      as Serialise


-- | A generic "data" type.
--
-- The main constructor 'Constr' represents a datatype value in sum-of-products
-- form: @Constr i args@ represents a use of the @i@th constructor along with its arguments.
--
-- The other constructors are various primitives.
data Data =
      Constr Integer [Data]
    | Map [(Data, Data)]
    | I Integer
    | B ByteString
    deriving (Show, Eq, Ord)

type CBORToDataError = String

-- TODO: handle indefinite versions, use view-patterns or something
-- TODO: try and make this match the serialization of Haskell types using derived 'Serialise'?
-- Would at least need to handle special cases with Null etc.
fromTerm :: CBOR.Term -> Either CBORToDataError Data
fromTerm = \case
    CBOR.TInteger i -> pure $ I i
    CBOR.TBytes b -> pure $ B $ BSL.fromStrict b
    CBOR.TMap entries -> Map <$> traverse (bitraverse fromTerm fromTerm) entries
    CBOR.TTagged i (CBOR.TList entries) -> Constr (fromIntegral i) <$> traverse fromTerm entries
    t -> Left $ "Unsupported CBOR term: " ++ show t

toTerm :: Data -> CBOR.Term
toTerm = \case
    I i -> CBOR.TInteger i
    B b -> CBOR.TBytes $ BSL.toStrict b
    Map entries -> CBOR.TMap (fmap (bimap toTerm toTerm) entries)
    Constr i entries -> CBOR.TTagged (fromIntegral i) $ CBOR.TList $ fmap toTerm entries

instance Serialise.Serialise Data where
    encode = Serialise.encode . toTerm
    decode = do
        term <- Serialise.decode
        case fromTerm term of
            Left msg -> fail $ "Failed to decode from CBOR term: " ++ msg
            Right d  -> pure d
