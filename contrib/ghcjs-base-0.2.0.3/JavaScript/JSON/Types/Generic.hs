{-# LANGUAGE CPP, DefaultSignatures, EmptyDataDecls, FlexibleInstances,
    FunctionalDependencies, KindSignatures, OverlappingInstances,
    ScopedTypeVariables, TypeOperators, UndecidableInstances,
    ViewPatterns, NamedFieldPuns, FlexibleContexts, PatternGuards,
    RecordWildCards, DataKinds #-}

-- |
-- Module:      Data.Aeson.Types.Generic
-- Copyright:   (c) 2012 Bryan O'Sullivan
--              (c) 2011, 2012 Bas Van Dijk
--              (c) 2011 MailRank, Inc.
-- License:     Apache
-- Maintainer:  Bryan O'Sullivan <bos@serpentine.com>
-- Stability:   experimental
-- Portability: portable
--
-- Types for working with JSON data.

module JavaScript.JSON.Types.Generic ( ) where

import Control.Applicative ((<*>), (<$>), (<|>), pure)
import Control.Monad ((<=<))
import Control.Monad.ST (ST)
import JavaScript.Array (JSArray)
import JavaScript.JSON.Types.Instances
import JavaScript.JSON.Types.Internal
import qualified Data.JSString as JSS
import qualified JavaScript.JSON.Types.Internal as I
import qualified JavaScript.Array as JSA
import qualified JavaScript.Array.ST as JSAST
import Data.Bits

import Data.DList (DList, toList, empty)

import Data.JSString (JSString, pack, unpack)
import Data.Maybe (fromMaybe)
import Data.Monoid (mappend)

-- import Data.Text (Text, pack, unpack)

import GHC.Generics

{-
import qualified Data.HashMap.Strict as H
import qualified Data.Vector as V
import qualified Data.Vector.Mutable as VM
-}
--------------------------------------------------------------------------------
-- Generic toJSON

instance (GToJSON a) => GToJSON (M1 i c a) where
    -- Meta-information, which is not handled elsewhere, is ignored:
    gToJSON opts = gToJSON opts . unM1
    {-# INLINE gToJSON #-}

instance (ToJSON a) => GToJSON (K1 i a) where
    -- Constant values are encoded using their ToJSON instance:
    gToJSON _opts = toJSON . unK1
    {-# INLINE gToJSON #-}

instance GToJSON U1 where
    -- Empty constructors are encoded to an empty array:
    gToJSON _opts _ = emptyArray
    {-# INLINE gToJSON #-}

instance (ConsToJSON a) => GToJSON (C1 c a) where
    -- Constructors need to be encoded differently depending on whether they're
    -- a record or not. This distinction is made by 'constToJSON':
    gToJSON opts = consToJSON opts . unM1
    {-# INLINE gToJSON #-}

instance ( WriteProduct a, WriteProduct b
         , ProductSize  a, ProductSize  b ) => GToJSON (a :*: b) where
    -- Products are encoded to an array. Here we allocate a mutable vector of
    -- the same size as the product and write the product's elements to it using
    -- 'writeProduct':
    gToJSON opts p =
        arrayValue $ JSAST.build $ \a ->
          writeProduct opts a 0 lenProduct p
        where
          lenProduct = (unTagged2 :: Tagged2 (a :*: b) Int -> Int)
                       productSize
    {-# INLINE gToJSON #-}

instance ( AllNullary (a :+: b) allNullary
         , SumToJSON  (a :+: b) allNullary ) => GToJSON (a :+: b) where
    -- If all constructors of a sum datatype are nullary and the
    -- 'allNullaryToStringTag' option is set they are encoded to
    -- strings.  This distinction is made by 'sumToJSON':
    gToJSON opts = (unTagged :: Tagged allNullary Value -> Value)
                 . sumToJSON opts
    {-# INLINE gToJSON #-}

--------------------------------------------------------------------------------

class SumToJSON f allNullary where
    sumToJSON :: Options -> f a -> Tagged allNullary Value

instance ( GetConName            f
         , TaggedObject          f
         , ObjectWithSingleField f
         , TwoElemArray          f ) => SumToJSON f True where
    sumToJSON opts
        | allNullaryToStringTag opts = Tagged . stringValue . pack
                                     . constructorTagModifier opts . getConName
        | otherwise = Tagged . nonAllNullarySumToJSON opts
    {-# INLINE sumToJSON #-}

instance ( TwoElemArray          f
         , TaggedObject          f
         , ObjectWithSingleField f ) => SumToJSON f False where
    sumToJSON opts = Tagged . nonAllNullarySumToJSON opts
    {-# INLINE sumToJSON #-}

nonAllNullarySumToJSON :: ( TwoElemArray          f
                          , TaggedObject          f
                          , ObjectWithSingleField f
                          ) => Options -> f a -> Value
nonAllNullarySumToJSON opts =
    case sumEncoding opts of
      TaggedObject{..}      -> objectValue . object . taggedObject opts tagFieldName
                                                          contentsFieldName
      ObjectWithSingleField -> objectValue . objectWithSingleField opts
      TwoElemArray          -> arrayValue  . twoElemArray opts
{-# INLINE nonAllNullarySumToJSON #-}

--------------------------------------------------------------------------------

class TaggedObject f where
    taggedObject :: Options -> String -> String -> f a -> [Pair]

instance ( TaggedObject a
         , TaggedObject b ) => TaggedObject (a :+: b) where
    taggedObject     opts tagFieldName contentsFieldName (L1 x) =
        taggedObject opts tagFieldName contentsFieldName     x
    taggedObject     opts tagFieldName contentsFieldName (R1 x) =
        taggedObject opts tagFieldName contentsFieldName     x
    {-# INLINE taggedObject #-}

instance ( IsRecord      a isRecord
         , TaggedObject' a isRecord
         , Constructor c ) => TaggedObject (C1 c a) where
    taggedObject opts tagFieldName contentsFieldName =
        (pack tagFieldName .= constructorTagModifier opts
                                 (conName (undefined :: t c a p)) :) .
        (unTagged :: Tagged isRecord [Pair] -> [Pair]) .
          taggedObject' opts contentsFieldName . unM1
    {-# INLINE taggedObject #-}

class TaggedObject' f isRecord where
    taggedObject' :: Options -> String -> f a -> Tagged isRecord [Pair]

instance (RecordToPairs f) => TaggedObject' f True where
    taggedObject' opts _ = Tagged . toList . recordToPairs opts
    {-# INLINE taggedObject' #-}

instance (GToJSON f) => TaggedObject' f False where
    taggedObject' opts contentsFieldName =
        Tagged . (:[]) . (pack contentsFieldName .=) . gToJSON opts
    {-# INLINE taggedObject' #-}

--------------------------------------------------------------------------------

-- | Get the name of the constructor of a sum datatype.
class GetConName f where
    getConName :: f a -> String

instance (GetConName a, GetConName b) => GetConName (a :+: b) where
    getConName (L1 x) = getConName x
    getConName (R1 x) = getConName x
    {-# INLINE getConName #-}

instance (Constructor c, GToJSON a, ConsToJSON a) => GetConName (C1 c a) where
    getConName = conName
    {-# INLINE getConName #-}

--------------------------------------------------------------------------------

class TwoElemArray f where
    twoElemArray :: Options -> f a -> JSArray -- V.Vector Value

instance (TwoElemArray a, TwoElemArray b) => TwoElemArray (a :+: b) where
    twoElemArray opts (L1 x) = twoElemArray opts x
    twoElemArray opts (R1 x) = twoElemArray opts x
    {-# INLINE twoElemArray #-}

instance ( GToJSON a, ConsToJSON a
         , Constructor c ) => TwoElemArray (C1 c a) where
    twoElemArray opts x = arrayValueList
      [ stringValue $ JSS.pack $ constructorTagModifier opts $ conName (undefined :: t c a p)
      , gToJSON opts x
      ]
    {-# INLINE twoElemArray #-}

--------------------------------------------------------------------------------

class ConsToJSON f where
    consToJSON  :: Options -> f a -> Value

class ConsToJSON' f isRecord where
    consToJSON' :: Options -> f a -> Tagged isRecord Value

instance ( IsRecord    f isRecord
         , ConsToJSON' f isRecord ) => ConsToJSON f where
    consToJSON opts = (unTagged :: Tagged isRecord Value -> Value)
                    . consToJSON' opts
    {-# INLINE consToJSON #-}

instance (RecordToPairs f) => ConsToJSON' f True where
    consToJSON' opts = Tagged . objectValue . object . toList . recordToPairs opts
    {-# INLINE consToJSON' #-}

instance GToJSON f => ConsToJSON' f False where
    consToJSON' opts = Tagged . gToJSON opts
    {-# INLINE consToJSON' #-}

--------------------------------------------------------------------------------

class RecordToPairs f where
    recordToPairs :: Options -> f a -> DList Pair

instance (RecordToPairs a, RecordToPairs b) => RecordToPairs (a :*: b) where
    recordToPairs opts (a :*: b) = recordToPairs opts a `mappend`
                                   recordToPairs opts b
    {-# INLINE recordToPairs #-}

instance (Selector s, GToJSON a) => RecordToPairs (S1 s a) where
    recordToPairs = fieldToPair
    {-# INLINE recordToPairs #-}

instance (Selector s, ToJSON a) => RecordToPairs (S1 s (K1 i (Maybe a))) where
    recordToPairs opts (M1 k1) | omitNothingFields opts
                               , K1 Nothing <- k1 = empty
    recordToPairs opts m1 = fieldToPair opts m1
    {-# INLINE recordToPairs #-}

fieldToPair :: (Selector s, GToJSON a) => Options -> S1 s a p -> DList Pair
fieldToPair opts m1 = pure ( pack $ fieldLabelModifier opts $ selName m1
                           , gToJSON opts (unM1 m1)
                           )
{-# INLINE fieldToPair #-}

--------------------------------------------------------------------------------

class WriteProduct f where
    writeProduct :: Options
                 -> JSAST.STJSArray s
                 -> Int -- ^ index
                 -> Int -- ^ length
                 -> f a
                 -> ST s ()

instance ( WriteProduct a
         , WriteProduct b ) => WriteProduct (a :*: b) where
    writeProduct opts mv ix len (a :*: b) = do
      writeProduct opts mv ix  lenL a
      writeProduct opts mv ixR lenR b
        where
#if MIN_VERSION_base(4,5,0)
          lenL = len `unsafeShiftR` 1
#else
          lenL = len `shiftR` 1
#endif
          lenR = len - lenL
          ixR  = ix  + lenL
    {-# INLINE writeProduct #-}

instance (GToJSON a) => WriteProduct a where
    writeProduct opts mv ix _ = (\(SomeValue v) -> JSAST.write ix v mv) . gToJSON opts
    {-# INLINE writeProduct #-}

--------------------------------------------------------------------------------

class ObjectWithSingleField f where
    objectWithSingleField :: Options -> f a -> Object

instance ( ObjectWithSingleField a
         , ObjectWithSingleField b ) => ObjectWithSingleField (a :+: b) where
    objectWithSingleField opts (L1 x) = objectWithSingleField opts x
    objectWithSingleField opts (R1 x) = objectWithSingleField opts x
    {-# INLINE objectWithSingleField #-}

instance ( GToJSON a, ConsToJSON a
         , Constructor c ) => ObjectWithSingleField (C1 c a) where
    objectWithSingleField opts x = I.object [(typ, gToJSON opts x)]
        where
          typ = pack $ constructorTagModifier opts $
                         conName (undefined :: t c a p)
    {-# INLINE objectWithSingleField #-}

--------------------------------------------------------------------------------
-- Generic parseJSON

instance (GFromJSON a) => GFromJSON (M1 i c a) where
    -- Meta-information, which is not handled elsewhere, is just added to the
    -- parsed value:
    gParseJSON opts = fmap M1 . gParseJSON opts
    {-# INLINE gParseJSON #-}

instance (FromJSON a) => GFromJSON (K1 i a) where
    -- Constant values are decoded using their FromJSON instance:
    gParseJSON _opts = fmap K1 . parseJSON
    {-# INLINE gParseJSON #-}

instance GFromJSON U1 where
    -- Empty constructors are expected to be encoded as an empty array:
    gParseJSON _opts v
        | isEmptyArray v = pure U1
        | otherwise      = typeMismatch "unit constructor (U1)" v
    {-# INLINE gParseJSON #-}

instance (ConsFromJSON a) => GFromJSON (C1 c a) where
    -- Constructors need to be decoded differently depending on whether they're
    -- a record or not. This distinction is made by consParseJSON:
    gParseJSON opts = fmap M1 . consParseJSON opts
    {-# INLINE gParseJSON #-}

instance ( FromProduct a, FromProduct b
         , ProductSize a, ProductSize b ) => GFromJSON (a :*: b) where
    -- Products are expected to be encoded to an array. Here we check whether we
    -- got an array of the same size as the product, then parse each of the
    -- product's elements using parseProduct:
    gParseJSON opts = withArray "product (:*:)" $ \arr ->
      let lenArray = JSA.length arr
          lenProduct = (unTagged2 :: Tagged2 (a :*: b) Int -> Int)
                       productSize in
      if lenArray == lenProduct
      then parseProduct opts arr 0 lenProduct
      else fail $ "When expecting a product of " ++ show lenProduct ++
                  " values, encountered an Array of " ++ show lenArray ++
                  " elements instead"
    {-# INLINE gParseJSON #-}

instance ( AllNullary (a :+: b) allNullary
         , ParseSum   (a :+: b) allNullary ) => GFromJSON   (a :+: b) where
    -- If all constructors of a sum datatype are nullary and the
    -- 'allNullaryToStringTag' option is set they are expected to be
    -- encoded as strings.  This distinction is made by 'parseSum':
    gParseJSON opts = (unTagged :: Tagged allNullary (Parser ((a :+: b) d)) ->
                                                     (Parser ((a :+: b) d)))
                    . parseSum opts
    {-# INLINE gParseJSON #-}

--------------------------------------------------------------------------------

class ParseSum f allNullary where
    parseSum :: Options -> Value -> Tagged allNullary (Parser (f a))

instance ( SumFromString    (a :+: b)
         , FromPair         (a :+: b)
         , FromTaggedObject (a :+: b) ) => ParseSum (a :+: b) True where
    parseSum opts
        | allNullaryToStringTag opts = Tagged . parseAllNullarySum    opts
        | otherwise                  = Tagged . parseNonAllNullarySum opts
    {-# INLINE parseSum #-}

instance ( FromPair         (a :+: b)
         , FromTaggedObject (a :+: b) ) => ParseSum (a :+: b) False where
    parseSum opts = Tagged . parseNonAllNullarySum opts
    {-# INLINE parseSum #-}

--------------------------------------------------------------------------------

parseAllNullarySum :: SumFromString f => Options -> Value -> Parser (f a)
parseAllNullarySum opts = withJSString "Text" $ \key ->
                            maybe (notFound $ unpack key) return $
                              parseSumFromString opts key
{-# INLINE parseAllNullarySum #-}

class SumFromString f where
    parseSumFromString :: Options -> JSString -> Maybe (f a)

instance (SumFromString a, SumFromString b) => SumFromString (a :+: b) where
    parseSumFromString opts key = (L1 <$> parseSumFromString opts key) <|>
                                  (R1 <$> parseSumFromString opts key)
    {-# INLINE parseSumFromString #-}

instance (Constructor c) => SumFromString (C1 c U1) where
    parseSumFromString opts key | key == name = Just $ M1 U1
                                | otherwise   = Nothing
        where
          name = pack $ constructorTagModifier opts $
                          conName (undefined :: t c U1 p)
    {-# INLINE parseSumFromString #-}

--------------------------------------------------------------------------------

parseNonAllNullarySum :: ( FromPair                       (a :+: b)
                         , FromTaggedObject               (a :+: b)
                         ) => Options -> Value -> Parser ((a :+: b) c)
parseNonAllNullarySum opts =
    case sumEncoding opts of
      TaggedObject{..} ->
          withObject "Object" $ \obj -> do
            tag <- obj .: pack tagFieldName
            fromMaybe (notFound $ unpack tag) $
              parseFromTaggedObject opts contentsFieldName obj tag

      ObjectWithSingleField ->
          withObject "Object" $ \obj ->
            case objectAssocs obj of
              [pair@(tag, _)] -> fromMaybe (notFound $ unpack tag) $
                                   parsePair opts pair
              _ -> fail "Object doesn't have a single field"

      TwoElemArray ->
          withArray "Array" $ \arr ->
            if JSA.length arr == 2
            then case match (indexV arr 0) of
                   String tag -> fromMaybe (notFound $ unpack tag) $
                                   parsePair opts (tag, indexV arr 1)
                   _ -> fail "First element is not a String"
            else fail "Array doesn't have 2 elements"
{-# INLINE parseNonAllNullarySum #-}

--------------------------------------------------------------------------------

class FromTaggedObject f where
    parseFromTaggedObject :: Options -> String -> Object -> JSString
                          -> Maybe (Parser (f a))

instance (FromTaggedObject a, FromTaggedObject b) =>
    FromTaggedObject (a :+: b) where
        parseFromTaggedObject opts contentsFieldName obj tag =
            (fmap L1 <$> parseFromTaggedObject opts contentsFieldName obj tag) <|>
            (fmap R1 <$> parseFromTaggedObject opts contentsFieldName obj tag)
        {-# INLINE parseFromTaggedObject #-}

instance ( FromTaggedObject' f
         , Constructor c ) => FromTaggedObject (C1 c f) where
    parseFromTaggedObject opts contentsFieldName obj tag
        | tag == name = Just $ M1 <$> parseFromTaggedObject'
                                        opts contentsFieldName obj
        | otherwise = Nothing
        where
          name = pack $ constructorTagModifier opts $
                          conName (undefined :: t c f p)
    {-# INLINE parseFromTaggedObject #-}

--------------------------------------------------------------------------------

class FromTaggedObject' f where
    parseFromTaggedObject' :: Options -> String -> Object -> Parser (f a)

class FromTaggedObject'' f isRecord where
    parseFromTaggedObject'' :: Options -> String -> Object
                            -> Tagged isRecord (Parser (f a))

instance ( IsRecord             f isRecord
         , FromTaggedObject''   f isRecord
         ) => FromTaggedObject' f where
    parseFromTaggedObject' opts contentsFieldName =
        (unTagged :: Tagged isRecord (Parser (f a)) -> Parser (f a)) .
        parseFromTaggedObject'' opts contentsFieldName
    {-# INLINE parseFromTaggedObject' #-}

instance (FromRecord f) => FromTaggedObject'' f True where
    parseFromTaggedObject'' opts _ = Tagged . parseRecord opts
    {-# INLINE parseFromTaggedObject'' #-}

instance (GFromJSON f) => FromTaggedObject'' f False where
    parseFromTaggedObject'' opts contentsFieldName = Tagged .
      (gParseJSON opts <=< (.: pack contentsFieldName))
    {-# INLINE parseFromTaggedObject'' #-}

--------------------------------------------------------------------------------

class ConsFromJSON f where
    consParseJSON  :: Options -> Value -> Parser (f a)

class ConsFromJSON' f isRecord where
    consParseJSON' :: Options -> Value -> Tagged isRecord (Parser (f a))

instance ( IsRecord        f isRecord
         , ConsFromJSON'   f isRecord
         ) => ConsFromJSON f where
    consParseJSON opts = (unTagged :: Tagged isRecord (Parser (f a)) -> Parser (f a))
                       . consParseJSON' opts
    {-# INLINE consParseJSON #-}

instance (FromRecord f) => ConsFromJSON' f True where
    consParseJSON' opts = Tagged . (withObject "record (:*:)" $ parseRecord opts)
    {-# INLINE consParseJSON' #-}

instance (GFromJSON f) => ConsFromJSON' f False where
    consParseJSON' opts = Tagged . gParseJSON opts
    {-# INLINE consParseJSON' #-}

--------------------------------------------------------------------------------

class FromRecord f where
    parseRecord :: Options -> Object -> Parser (f a)

instance (FromRecord a, FromRecord b) => FromRecord (a :*: b) where
    parseRecord opts obj = (:*:) <$> parseRecord opts obj
                                 <*> parseRecord opts obj
    {-# INLINE parseRecord #-}

instance (Selector s, GFromJSON a) => FromRecord (S1 s a) where
    parseRecord opts = maybe (notFound label) (gParseJSON opts)
                      . I.lookup (pack label)
        where
          label = fieldLabelModifier opts $ selName (undefined :: t s a p)
    {-# INLINE parseRecord #-}

instance (Selector s, FromJSON a) => FromRecord (S1 s (K1 i (Maybe a))) where
    parseRecord opts obj = (M1 . K1) <$> obj .:? pack label
        where
          label = fieldLabelModifier opts $
                    selName (undefined :: t s (K1 i (Maybe a)) p)
    {-# INLINE parseRecord #-}

--------------------------------------------------------------------------------

class ProductSize f where
    productSize :: Tagged2 f Int

instance (ProductSize a, ProductSize b) => ProductSize (a :*: b) where
    productSize = Tagged2 $ unTagged2 (productSize :: Tagged2 a Int) +
                            unTagged2 (productSize :: Tagged2 b Int)
    {-# INLINE productSize #-}

instance ProductSize (S1 s a) where
    productSize = Tagged2 1
    {-# INLINE productSize #-}

--------------------------------------------------------------------------------

class FromProduct f where
    parseProduct :: Options -> JSArray -> Int -> Int -> Parser (f a)

instance (FromProduct a, FromProduct b) => FromProduct (a :*: b) where
    parseProduct opts arr ix len =
        (:*:) <$> parseProduct opts arr ix  lenL
              <*> parseProduct opts arr ixR lenR
        where
#if MIN_VERSION_base(4,5,0)
          lenL = len `unsafeShiftR` 1
#else
          lenL = len `shiftR` 1
#endif
          ixR  = ix + lenL
          lenR = len - lenL
    {-# INLINE parseProduct #-}

instance (GFromJSON a) => FromProduct (S1 s a) where
    parseProduct opts arr ix _ = gParseJSON opts $ indexV arr ix
    {-# INLINE parseProduct #-}

--------------------------------------------------------------------------------

class FromPair f where
    parsePair :: Options -> Pair -> Maybe (Parser (f a))

instance (FromPair a, FromPair b) => FromPair (a :+: b) where
    parsePair opts pair = (fmap L1 <$> parsePair opts pair) <|>
                          (fmap R1 <$> parsePair opts pair)
    {-# INLINE parsePair #-}

instance (Constructor c, GFromJSON a, ConsFromJSON a) => FromPair (C1 c a) where
    parsePair opts (tag, value)
        | tag == tag' = Just $ gParseJSON opts value
        | otherwise   = Nothing
        where
          tag' = pack $ constructorTagModifier opts $
                          conName (undefined :: t c a p)
    {-# INLINE parsePair #-}

--------------------------------------------------------------------------------

class IsRecord (f :: * -> *) isRecord | f -> isRecord

instance (IsRecord f isRecord) => IsRecord (f :*: g) isRecord
#if MIN_VERSION_base(4,9,0)
instance IsRecord (M1 S ('MetaSel 'Nothing u ss ds) f) False
#else
instance IsRecord (M1 S NoSelector f) False
#endif
instance (IsRecord f isRecord) => IsRecord (M1 S c f) isRecord
instance IsRecord (K1 i c) True
instance IsRecord U1 False

--------------------------------------------------------------------------------

class AllNullary (f :: * -> *) allNullary | f -> allNullary

instance ( AllNullary a allNullaryL
         , AllNullary b allNullaryR
         , And allNullaryL allNullaryR allNullary
         ) => AllNullary (a :+: b) allNullary
instance AllNullary a allNullary => AllNullary (M1 i c a) allNullary
instance AllNullary (a :*: b) False
instance AllNullary (K1 i c) False
instance AllNullary U1 True

--------------------------------------------------------------------------------

data True
data False

class    And bool1 bool2 bool3 | bool1 bool2 -> bool3

instance And True  True  True
instance And False False False
instance And False True  False
instance And True  False False

--------------------------------------------------------------------------------

newtype Tagged s b = Tagged {unTagged :: b}

newtype Tagged2 (s :: * -> *) b = Tagged2 {unTagged2 :: b}

--------------------------------------------------------------------------------

notFound :: String -> Parser a
notFound key = fail $ "The key \"" ++ key ++ "\" was not found"
{-# INLINE notFound #-}
