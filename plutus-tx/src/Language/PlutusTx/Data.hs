{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE LambdaCase         #-}
{-# LANGUAGE OverloadedStrings  #-}
{-# LANGUAGE ViewPatterns       #-}
module Language.PlutusTx.Data (Data (..), fromTerm, toTerm) where

import           Prelude                   hiding (fail)

import           Data.Bifunctor            (bimap)
import           Data.Bitraversable        (bitraverse)
import           Data.ByteString.Lazy      as BSL

import           Control.Monad.Fail

import qualified Codec.CBOR.Term           as CBOR
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
    | B ByteString
    deriving stock (Show, Eq, Ord, Generic)

instance Pretty Data where
    pretty = \case
        Constr _ ds -> angles (sep (punctuate comma (fmap pretty ds)))
        Map entries -> braces (sep (punctuate comma (fmap (\(k, v) -> pretty k <> ":" <+> pretty v) entries)))
        List ds -> brackets (sep (punctuate comma (fmap pretty ds)))
        I i -> pretty i
        B b -> viaShow b

type CBORToDataError = String

{- Note [Permissive decoding]
We're using a canonical representation of lists, maps, bytes, and integers. However,
the CBOR library does not guarantee that a TInteger gets encoded as a big integer,
so we can't rely on getting back our canonical version when we decode (see
https://github.com/well-typed/cborg/issues/222). So we need to be permissive
when we decode.
-}

viewList :: CBOR.Term -> Maybe [CBOR.Term]
viewList (CBOR.TList l)  = Just l
viewList (CBOR.TListI l) = Just l
viewList _               = Nothing

viewMap :: CBOR.Term -> Maybe [(CBOR.Term, CBOR.Term)]
viewMap (CBOR.TMap m)  = Just m
viewMap (CBOR.TMapI m) = Just m
viewMap _              = Nothing

viewBytes :: CBOR.Term -> Maybe ByteString
viewBytes (CBOR.TBytes b)  = Just (BSL.fromStrict b)
viewBytes (CBOR.TBytesI b) = Just b
viewBytes _                = Nothing

viewInteger :: CBOR.Term -> Maybe Integer
viewInteger (CBOR.TInt i)     = Just (fromIntegral i)
viewInteger (CBOR.TInteger i) = Just i
viewInteger _                 = Nothing

-- TODO: try and make this match the serialization of Haskell types using derived 'Serialise'?
-- Would at least need to handle special cases with Null etc.
fromTerm :: CBOR.Term -> Either CBORToDataError Data
fromTerm = \case
    -- See Note [Permissive decoding]
    (viewInteger -> Just i) -> pure $ I i
    (viewBytes -> Just b) -> pure $ B b
    (viewMap -> Just entries) -> Map <$> traverse (bitraverse fromTerm fromTerm) entries
    (viewList -> Just ts) -> List <$> traverse fromTerm ts
    CBOR.TTagged i (viewList -> Just entries) -> Constr (fromIntegral i) <$> traverse fromTerm entries
    t -> Left $ "Unsupported CBOR term: " ++ show t

toTerm :: Data -> CBOR.Term
toTerm = \case
    I i -> CBOR.TInteger i
    B b -> CBOR.TBytes $ BSL.toStrict b
    Map entries -> CBOR.TMap (fmap (bimap toTerm toTerm) entries)
    List ts -> CBOR.TList (fmap toTerm ts)
    Constr i entries -> CBOR.TTagged (fromIntegral i) $ CBOR.TList $ fmap toTerm entries

instance Serialise.Serialise Data where
    encode = Serialise.encode . toTerm
    decode = do
        term <- Serialise.decode
        case fromTerm term of
            Left msg -> fail $ "Failed to decode from CBOR term: " ++ msg
            Right d  -> pure d
