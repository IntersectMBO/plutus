{-# LANGUAGE CPP, DeriveDataTypeable, FlexibleContexts, FlexibleInstances,
    GeneralizedNewtypeDeriving, IncoherentInstances, OverlappingInstances,
    OverloadedStrings, UndecidableInstances, ViewPatterns #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

{-# LANGUAGE DefaultSignatures #-}

-- |
-- Module:      Data.Aeson.Types.Instances
-- Copyright:   (c) 2011-2013 Bryan O'Sullivan
--              (c) 2011 MailRank, Inc.
-- License:     Apache
-- Maintainer:  Bryan O'Sullivan <bos@serpentine.com>
-- Stability:   experimental
-- Portability: portable
--
-- Types for working with JSON data.

module JavaScript.JSON.Types.Instances
    (
    -- * Type classes
    -- ** Core JSON classes
      FromJSON(..)
    , ToJSON(..)

    -- ** Generic JSON classes
    , GFromJSON(..)
    , GToJSON(..)
    , genericToJSON
    , genericParseJSON

    -- * Types
    , DotNetTime(..)

      -- * Inspecting @'Value's@
    , withObject
    , withJSString
    , withArray
    , withDouble
    , withBool

    -- * Functions
    , fromJSON
    , (.:)
    , (.:?)
    , (.!=)
    , (.=)
    , typeMismatch
    ) where

import Control.Applicative ((<$>), (<*>), (<|>), pure, empty)
-- import Data.Aeson.Functions
-- import JavaScript.JSON.Functions
-- import Data.Aeson.Types.Class

-- import Data.Aeson.Types.Internal

import           Data.JSString      (JSString)
import qualified Data.JSString      as JSS
import qualified Data.JSString.Text as JSS

import           JavaScript.Array (JSArray)
import qualified JavaScript.Array as JSA

import JavaScript.JSON.Types.Class
import JavaScript.JSON.Types.Internal
import qualified JavaScript.JSON.Types.Internal as I

import Data.Scientific (Scientific)
import qualified Data.Scientific as Scientific (coefficient, base10Exponent, fromFloatDigits, toRealFloat)
import Data.Attoparsec.Number (Number(..))
import Data.Fixed
import Data.Hashable (Hashable(..))
import Data.Int (Int8, Int16, Int32, Int64)
import Data.Maybe (fromMaybe)
import Data.Monoid (Dual(..), First(..), Last(..), mappend)
import Data.Ratio (Ratio, (%), numerator, denominator)
import Data.Text (Text, pack, unpack)
import Data.Time (UTCTime, ZonedTime(..), TimeZone(..))
import Data.Time.Format (FormatTime, formatTime, parseTime)
import Data.Traversable (traverse)
import Data.Vector (Vector)
import Data.Word (Word, Word8, Word16, Word32, Word64)
import Foreign.Storable (Storable)
-- #if MIN_VERSION_time(1,5,0)
import Data.Time.Format(defaultTimeLocale, dateTimeFmt)
-- #else
-- import System.Locale (defaultTimeLocale, dateTimeFmt)
-- #endif
import Unsafe.Coerce

import qualified Data.HashMap.Strict as H
import qualified Data.HashSet as HashSet
import qualified Data.IntMap as IntMap
import qualified Data.IntSet as IntSet
import qualified Data.Map as M
import qualified Data.Set as Set
import qualified Data.Tree as Tree
import qualified Data.Text as T
import qualified Data.Text.Lazy as LT
import qualified Data.Vector as V
import qualified Data.Vector.Generic as VG
import qualified Data.Vector.Primitive as VP
import qualified Data.Vector.Storable as VS
import qualified Data.Vector.Unboxed as VU
import qualified Data.Vector.Mutable as VM ( unsafeNew, unsafeWrite )

instance (ToJSON a) => ToJSON (Maybe a) where
    toJSON (Just a) = toJSON a
    toJSON Nothing  = nullValue
    {-# INLINE toJSON #-}

instance (FromJSON a) => FromJSON (Maybe a) where
    parseJSON (match -> Null) = pure Nothing
    parseJSON a               = Just <$> parseJSON a
    {-# INLINE parseJSON #-}

instance (ToJSON a, ToJSON b) => ToJSON (Either a b) where
    toJSON (Left a)  = objectValue $ object [left  .= a]
    toJSON (Right b) = objectValue $ object [right .= b]
    {-# INLINE toJSON #-}

instance (FromJSON a, FromJSON b) => FromJSON (Either a b) where
    parseJSON (match -> (Object (objectAssocs -> [(key, value)])))
        | key == left  = Left  <$> parseJSON value
        | key == right = Right <$> parseJSON value
    parseJSON _        = fail $
        "expected an object with a single property " ++
        "where the property key should be either " ++
        "\"Left\" or \"Right\""
    {-# INLINE parseJSON #-}

left, right :: JSString
left  = "Left"
right = "Right"

instance ToJSON Bool where
    toJSON = boolValue
    {-# INLINE toJSON #-}

instance FromJSON Bool where
    parseJSON = withBool "Bool" pure
    {-# INLINE parseJSON #-}

instance ToJSON () where
    toJSON _ = emptyArray
    {-# INLINE toJSON #-}

instance FromJSON () where
    parseJSON = withArray "()" $ \v ->
                  if JSA.null v
                    then pure ()
                    else fail "Expected an empty array"
    {-# INLINE parseJSON #-}

instance ToJSON [Char] where
    toJSON = stringValue . JSS.pack
    {-# INLINE toJSON #-}

instance FromJSON [Char] where
    parseJSON = withJSString "String" $ pure . JSS.unpack
    {-# INLINE parseJSON #-}

instance ToJSON Char where
    toJSON = stringValue . JSS.singleton
    {-# INLINE toJSON #-}

instance FromJSON Char where
    parseJSON = withJSString "Char" $ \t ->
                  if JSS.compareLength t 1 == EQ
                    then pure $ JSS.head t
                    else fail "Expected a string of length 1"
    {-# INLINE parseJSON #-}

{-
instance ToJSON Scientific where
    toJSON = Number
    {-# INLINE toJSON #-}

instance FromJSON Scientific where
    parseJSON = withScientific "Scientific" pure
    {-# INLINE parseJSON #-}
-}

instance ToJSON Double where
    toJSON = doubleValue
    {-# INLINE toJSON #-}

instance FromJSON Double where
    parseJSON = withDouble "Double" pure
    {-# INLINE parseJSON #-}

{-
instance ToJSON Number where
    toJSON (D d) = toJSON d
    toJSON (I i) = toJSON i
    {-# INLINE toJSON #-}

instance FromJSON Number where
    parseJSON (Number s) = pure $ scientificToNumber s
    parseJSON Null       = pure (D (0/0))
    parseJSON v          = typeMismatch "Number" v
    {-# INLINE parseJSON #-}
-}

instance ToJSON Float where
    toJSON = doubleValue . realToFrac -- realFloatToJSON
    {-# INLINE toJSON #-}

instance FromJSON Float where
    parseJSON = withDouble "Float" (pure . realToFrac)
    {-# INLINE parseJSON #-}

instance ToJSON (Ratio Integer) where
    toJSON r = objectValue $ object [ "numerator"   .= numerator   r
                                    , "denominator" .= denominator r
                                    ]
    {-# INLINE toJSON #-}

instance FromJSON (Ratio Integer) where
    parseJSON = withObject "Rational" $ \obj ->
                  (%) <$> obj .: "numerator"
                      <*> obj .: "denominator"
    {-# INLINE parseJSON #-}

instance HasResolution a => ToJSON (Fixed a) where
    toJSON = doubleValue . realToFrac
    {-# INLINE toJSON #-}

-- | /WARNING:/ Only parse fixed-precision numbers from trusted input
-- since an attacker could easily fill up the memory of the target
-- system by specifying a scientific number with a big exponent like
-- @1e1000000000@.
instance HasResolution a => FromJSON (Fixed a) where
    parseJSON = withDouble "Fixed" $ pure . realToFrac
    {-# INLINE parseJSON #-}

instance ToJSON Int where
    toJSON = doubleValue . fromIntegral
    {-# INLINE toJSON #-}

instance FromJSON Int where
    parseJSON = parseIntegral "Int"
    {-# INLINE parseJSON #-}

instance ToJSON Integer where
    toJSON = doubleValue . fromInteger
    {-# INLINE toJSON #-}

-- | /WARNING:/ Only parse Integers from trusted input since an
-- attacker could easily fill up the memory of the target system by
-- specifying a scientific number with a big exponent like
-- @1e1000000000@.
instance FromJSON Integer where
    parseJSON = withDouble "Integral" $ pure . floor -- withScientific "Integral" $ pure . floor
    {-# INLINE parseJSON #-}

instance ToJSON Int8 where
    toJSON = doubleValue . fromIntegral
    {-# INLINE toJSON #-}

instance FromJSON Int8 where
    parseJSON = parseIntegral "Int8"
    {-# INLINE parseJSON #-}

instance ToJSON Int16 where
    toJSON = doubleValue . fromIntegral
    {-# INLINE toJSON #-}

instance FromJSON Int16 where
    parseJSON = parseIntegral "Int16"
    {-# INLINE parseJSON #-}

instance ToJSON Int32 where
    toJSON = doubleValue . fromIntegral
    {-# INLINE toJSON #-}

instance FromJSON Int32 where
    parseJSON = parseIntegral "Int32"
    {-# INLINE parseJSON #-}

instance ToJSON Int64 where
    toJSON = doubleValue . fromIntegral
    {-# INLINE toJSON #-}

instance FromJSON Int64 where
    parseJSON = parseIntegral "Int64"
    {-# INLINE parseJSON #-}

instance ToJSON Word where
    toJSON = doubleValue . fromIntegral
    {-# INLINE toJSON #-}

instance FromJSON Word where
    parseJSON = parseIntegral "Word"
    {-# INLINE parseJSON #-}

instance ToJSON Word8 where
    toJSON = doubleValue . fromIntegral
    {-# INLINE toJSON #-}

instance FromJSON Word8 where
    parseJSON = parseIntegral "Word8"
    {-# INLINE parseJSON #-}

instance ToJSON Word16 where
    toJSON = doubleValue . fromIntegral
    {-# INLINE toJSON #-}

instance FromJSON Word16 where
    parseJSON = parseIntegral "Word16"
    {-# INLINE parseJSON #-}

instance ToJSON Word32 where
    toJSON = doubleValue . fromIntegral
    {-# INLINE toJSON #-}

instance FromJSON Word32 where
    parseJSON = parseIntegral "Word32"
    {-# INLINE parseJSON #-}

instance ToJSON Word64 where
    toJSON = doubleValue . fromIntegral
    {-# INLINE toJSON #-}

instance FromJSON Word64 where
    parseJSON = parseIntegral "Word64"
    {-# INLINE parseJSON #-}

instance ToJSON JSString where
    toJSON = stringValue
    {-# INLINE toJSON #-}

instance FromJSON JSString where
    parseJSON = withJSString "JSString" pure
    {-# INLINE parseJSON #-}

instance ToJSON Text where
    toJSON = stringValue . JSS.textToJSString
    {-# INLINE toJSON #-}

instance FromJSON Text where
    parseJSON = withJSString "Text" ( pure . JSS.textFromJSString )
    {-# INLINE parseJSON #-}

instance ToJSON LT.Text where
    toJSON = stringValue . JSS.textToJSString . LT.toStrict
    {-# INLINE toJSON #-}

instance FromJSON LT.Text where
    parseJSON = withJSString "Lazy Text" $ pure . LT.fromStrict . JSS.textFromJSString
    {-# INLINE parseJSON #-}

instance (ToJSON a) => ToJSON [a] where
    toJSON = arrayValue . arrayValueList . map toJSON
    {-# INLINE toJSON #-}

instance (FromJSON a) => FromJSON [a] where
    parseJSON = withArray "[a]" $ mapM parseJSON . arrayToValueList
    {-# INLINE parseJSON #-}

{-
instance (ToJSON a) => ToJSON (Vector a) where
    toJSON = Array . V.map toJSON
    {-# INLINE toJSON #-}

instance (FromJSON a) => FromJSON (Vector a) where
    parseJSON = withArray "Vector a" $ V.mapM parseJSON
    {-# INLINE parseJSON #-}

vectorToJSON :: (VG.Vector v a, ToJSON a) => v a -> Value
vectorToJSON = Array . V.map toJSON . V.convert
{-# INLINE vectorToJSON #-}

vectorParseJSON :: (FromJSON a, VG.Vector w a) => String -> Value -> Parser (w a)
vectorParseJSON s = withArray s $ fmap V.convert . V.mapM parseJSON
{-# INLINE vectorParseJSON #-}

instance (Storable a, ToJSON a) => ToJSON (VS.Vector a) where
    toJSON = vectorToJSON

instance (Storable a, FromJSON a) => FromJSON (VS.Vector a) where
    parseJSON = vectorParseJSON "Data.Vector.Storable.Vector a"

instance (VP.Prim a, ToJSON a) => ToJSON (VP.Vector a) where
    toJSON = vectorToJSON

instance (VP.Prim a, FromJSON a) => FromJSON (VP.Vector a) where
    parseJSON = vectorParseJSON "Data.Vector.Primitive.Vector a"

instance (VG.Vector VU.Vector a, ToJSON a) => ToJSON (VU.Vector a) where
    toJSON = vectorToJSON

instance (VG.Vector VU.Vector a, FromJSON a) => FromJSON (VU.Vector a) where
    parseJSON = vectorParseJSON "Data.Vector.Unboxed.Vector a"
-}

instance (ToJSON a) => ToJSON (Set.Set a) where
    toJSON = toJSON . Set.toList
    {-# INLINE toJSON #-}

instance (Ord a, FromJSON a) => FromJSON (Set.Set a) where
    parseJSON = fmap Set.fromList . parseJSON
    {-# INLINE parseJSON #-}

instance (ToJSON a) => ToJSON (HashSet.HashSet a) where
    toJSON = toJSON . HashSet.toList
    {-# INLINE toJSON #-}

instance (Eq a, Hashable a, FromJSON a) => FromJSON (HashSet.HashSet a) where
    parseJSON = fmap HashSet.fromList . parseJSON
    {-# INLINE parseJSON #-}

instance ToJSON IntSet.IntSet where
    toJSON = toJSON . IntSet.toList
    {-# INLINE toJSON #-}

instance FromJSON IntSet.IntSet where
    parseJSON = fmap IntSet.fromList . parseJSON
    {-# INLINE parseJSON #-}

instance ToJSON a => ToJSON (IntMap.IntMap a) where
    toJSON = toJSON . IntMap.toList
    {-# INLINE toJSON #-}

instance FromJSON a => FromJSON (IntMap.IntMap a) where
    parseJSON = fmap IntMap.fromList . parseJSON
    {-# INLINE parseJSON #-}
{-
instance (ToJSON v) => ToJSON (M.Map Text v) where
    toJSON = Object . M.foldrWithKey (\k -> H.insert k . toJSON) H.empty
    {-# INLINE toJSON #-}

instance (FromJSON v) => FromJSON (M.Map Text v) where
    parseJSON = withObject "Map Text a" $
                  fmap (H.foldrWithKey M.insert M.empty) . traverse parseJSON

instance (ToJSON v) => ToJSON (M.Map LT.Text v) where
    toJSON = Object . mapHashKeyVal LT.toStrict toJSON

instance (FromJSON v) => FromJSON (M.Map LT.Text v) where
    parseJSON = fmap (hashMapKey LT.fromStrict) . parseJSON

instance (ToJSON v) => ToJSON (M.Map String v) where
    toJSON = Object . mapHashKeyVal pack toJSON

instance (FromJSON v) => FromJSON (M.Map String v) where
    parseJSON = fmap (hashMapKey unpack) . parseJSON

instance (ToJSON v) => ToJSON (H.HashMap Text v) where
    toJSON = Object . H.map toJSON
    {-# INLINE toJSON #-}

instance (FromJSON v) => FromJSON (H.HashMap Text v) where
    parseJSON = withObject "HashMap Text a" $ traverse parseJSON

instance (ToJSON v) => ToJSON (H.HashMap LT.Text v) where
    toJSON = Object . mapKeyVal LT.toStrict toJSON

instance (FromJSON v) => FromJSON (H.HashMap LT.Text v) where
    parseJSON = fmap (mapKey LT.fromStrict) . parseJSON

instance (ToJSON v) => ToJSON (H.HashMap String v) where
    toJSON = Object . mapKeyVal pack toJSON

instance (FromJSON v) => FromJSON (H.HashMap String v) where
    parseJSON = fmap (mapKey unpack) . parseJSON

instance (ToJSON v) => ToJSON (Tree.Tree v) where
    toJSON (Tree.Node root branches) = toJSON (root,branches)

instance (FromJSON v) => FromJSON (Tree.Tree v) where
    parseJSON j = uncurry Tree.Node <$> parseJSON j
-}

instance ToJSON Value where
    toJSON a = a
    {-# INLINE toJSON #-}

instance FromJSON Value where
    parseJSON a = pure a
    {-# INLINE parseJSON #-}

instance ToJSON DotNetTime where
    toJSON (DotNetTime t) =
        stringValue (JSS.pack (secs ++ formatMillis t ++ ")/"))
      where secs  = formatTime defaultTimeLocale "/Date(%s" t
    {-# INLINE toJSON #-}

instance FromJSON DotNetTime where
    parseJSON = withJSString "DotNetTime" $ \t ->
        let (s,m) = JSS.splitAt (JSS.length t - 5) t
            t'    = JSS.concat [s,".",m]
        in case parseTime defaultTimeLocale "/Date(%s%Q)/" (JSS.unpack t') of
             Just d -> pure (DotNetTime d)
             _      -> fail "could not parse .NET time"
    {-# INLINE parseJSON #-}

instance ToJSON ZonedTime where
    toJSON t = stringValue $ JSS.pack $ formatTime defaultTimeLocale format t
      where
        format = "%FT%T." ++ formatMillis t ++ tzFormat
        tzFormat
          | 0 == timeZoneMinutes (zonedTimeZone t) = "Z"
          | otherwise = "%z"

formatMillis :: (FormatTime t) => t -> String
formatMillis t = take 3 . formatTime defaultTimeLocale "%q" $ t

instance FromJSON ZonedTime where
    parseJSON (match -> String t) =
      tryFormats alternateFormats
      <|> fail "could not parse ECMA-262 ISO-8601 date"
      where
        tryFormat f =
          case parseTime defaultTimeLocale f (JSS.unpack t) of
            Just d -> pure d
            Nothing -> empty
        tryFormats = foldr1 (<|>) . map tryFormat
        alternateFormats =
          dateTimeFmt defaultTimeLocale :
          distributeList ["%Y", "%Y-%m", "%F"]
                         ["T%R", "T%T", "T%T%Q", "T%T%QZ", "T%T%Q%z"]

        distributeList xs ys =
          foldr (\x acc -> acc ++ distribute x ys) [] xs
        distribute x = map (mappend x)

    parseJSON v = typeMismatch "ZonedTime" v

instance ToJSON UTCTime where
    toJSON t = stringValue $ JSS.pack $ formatTime defaultTimeLocale format t
      where
        format = "%FT%T." ++ formatMillis t ++ "Z"
    {-# INLINE toJSON #-}

instance FromJSON UTCTime where
    parseJSON = withJSString "UTCTime" $ \t ->
        case parseTime defaultTimeLocale "%FT%T%QZ" (JSS.unpack t) of
          Just d -> pure d
          _      -> fail "could not parse ISO-8601 date"
    {-# INLINE parseJSON #-}

instance (ToJSON a, ToJSON b) => ToJSON (a,b) where
    toJSON (a,b) = arrayValue $ arrayValueList
      [toJSON a, toJSON b]
    {-# INLINE toJSON #-}

instance (FromJSON a, FromJSON b) => FromJSON (a,b) where
    parseJSON = withArray "(a,b)" $ \ab ->
        let n = JSA.length ab
        in if n == 2
             then (,) <$> parseJSON (indexV ab 0)
                      <*> parseJSON (indexV ab 1)
             else fail $ "cannot unpack array of length " ++
                         show n ++ " into a pair"
    {-# INLINE parseJSON #-}

instance (ToJSON a, ToJSON b, ToJSON c) => ToJSON (a,b,c) where
    toJSON (a,b,c) = arrayValue $ arrayValueList
      [toJSON a, toJSON b, toJSON c]
    {-# INLINE toJSON #-}

instance (FromJSON a, FromJSON b, FromJSON c) => FromJSON (a,b,c) where
    parseJSON = withArray "(a,b,c)" $ \abc ->
        let n = JSA.length abc
        in if n == 3
             then (,,) <$> parseJSON (indexV abc 0)
                       <*> parseJSON (indexV abc 1)
                       <*> parseJSON (indexV abc 2)
             else fail $ "cannot unpack array of length " ++
                          show n ++ " into a 3-tuple"
    {-# INLINE parseJSON #-}

instance (ToJSON a, ToJSON b, ToJSON c, ToJSON d) => ToJSON (a,b,c,d) where
    toJSON (a,b,c,d) = arrayValue $ arrayValueList
      [toJSON a, toJSON b, toJSON c, toJSON d]
    {-# INLINE toJSON #-}

instance (FromJSON a, FromJSON b, FromJSON c, FromJSON d) =>
         FromJSON (a,b,c,d) where
    parseJSON = withArray "(a,b,c,d)" $ \abcd ->
        let n = JSA.length abcd
        in if n == 4
             then (,,,) <$> parseJSON (indexV abcd 0)
                        <*> parseJSON (indexV abcd 1)
                        <*> parseJSON (indexV abcd 2)
                        <*> parseJSON (indexV abcd 3)
             else fail $ "cannot unpack array of length " ++
                         show n ++ " into a 4-tuple"
    {-# INLINE parseJSON #-}

instance (ToJSON a, ToJSON b, ToJSON c, ToJSON d, ToJSON e) =>
         ToJSON (a,b,c,d,e) where
    toJSON (a,b,c,d,e) = arrayValue $ arrayValueList
      [toJSON a, toJSON b, toJSON c, toJSON d, toJSON e]
    {-# INLINE toJSON #-}

instance (FromJSON a, FromJSON b, FromJSON c, FromJSON d, FromJSON e) =>
         FromJSON (a,b,c,d,e) where
    parseJSON = withArray "(a,b,c,d,e)" $ \abcde ->
        let n = JSA.length abcde
        in if n == 5
             then (,,,,) <$> parseJSON (indexV abcde 0)
                         <*> parseJSON (indexV abcde 1)
                         <*> parseJSON (indexV abcde 2)
                         <*> parseJSON (indexV abcde 3)
                         <*> parseJSON (indexV abcde 4)
             else fail $ "cannot unpack array of length " ++
                         show n ++ " into a 5-tuple"
    {-# INLINE parseJSON #-}

instance (ToJSON a, ToJSON b, ToJSON c, ToJSON d, ToJSON e, ToJSON f) =>
         ToJSON (a,b,c,d,e,f) where
    toJSON (a,b,c,d,e,f) = arrayValue $ arrayValueList
      [toJSON a, toJSON b, toJSON c, toJSON d, toJSON e, toJSON f]
    {-# INLINE toJSON #-}

instance (FromJSON a, FromJSON b, FromJSON c, FromJSON d, FromJSON e,
          FromJSON f) => FromJSON (a,b,c,d,e,f) where
    parseJSON = withArray "(a,b,c,d,e,f)" $ \abcdef ->
        let n = JSA.length abcdef
        in if n == 6
             then (,,,,,) <$> parseJSON (indexV abcdef 0)
                          <*> parseJSON (indexV abcdef 1)
                          <*> parseJSON (indexV abcdef 2)
                          <*> parseJSON (indexV abcdef 3)
                          <*> parseJSON (indexV abcdef 4)
                          <*> parseJSON (indexV abcdef 5)
             else fail $ "cannot unpack array of length " ++
                         show n ++ " into a 6-tuple"
    {-# INLINE parseJSON #-}

instance (ToJSON a, ToJSON b, ToJSON c, ToJSON d, ToJSON e, ToJSON f,
          ToJSON g) => ToJSON (a,b,c,d,e,f,g) where
    toJSON (a,b,c,d,e,f,g) = arrayValue $ arrayValueList
      [ toJSON a, toJSON b, toJSON c, toJSON d
      , toJSON e, toJSON f, toJSON g]
    {-# INLINE toJSON #-}

instance (FromJSON a, FromJSON b, FromJSON c, FromJSON d, FromJSON e,
          FromJSON f, FromJSON g) => FromJSON (a,b,c,d,e,f,g) where
    parseJSON = withArray "(a,b,c,d,e,f,g)" $ \abcdefg ->
        let n = JSA.length abcdefg
        in if n == 7
             then (,,,,,,) <$> parseJSON (indexV abcdefg 0)
                           <*> parseJSON (indexV abcdefg 1)
                           <*> parseJSON (indexV abcdefg 2)
                           <*> parseJSON (indexV abcdefg 3)
                           <*> parseJSON (indexV abcdefg 4)
                           <*> parseJSON (indexV abcdefg 5)
                           <*> parseJSON (indexV abcdefg 6)
             else fail $ "cannot unpack array of length " ++
                         show n ++ " into a 7-tuple"
    {-# INLINE parseJSON #-}

instance (ToJSON a, ToJSON b, ToJSON c, ToJSON d, ToJSON e, ToJSON f,
          ToJSON g, ToJSON h) => ToJSON (a,b,c,d,e,f,g,h) where
    toJSON (a,b,c,d,e,f,g,h) = arrayValue $ arrayValueList
      [ toJSON a, toJSON b, toJSON c, toJSON d
      , toJSON e, toJSON f, toJSON g, toJSON h]
    {-# INLINE toJSON #-}

instance (FromJSON a, FromJSON b, FromJSON c, FromJSON d, FromJSON e,
          FromJSON f, FromJSON g, FromJSON h) =>
         FromJSON (a,b,c,d,e,f,g,h) where
    parseJSON = withArray "(a,b,c,d,e,f,g,h)" $ \ary ->
        let n = JSA.length ary
        in if n /= 8
           then fail $ "cannot unpack array of length " ++
                       show n ++ " into an 8-tuple"
           else (,,,,,,,)
                <$> parseJSON (indexV ary 0)
                <*> parseJSON (indexV ary 1)
                <*> parseJSON (indexV ary 2)
                <*> parseJSON (indexV ary 3)
                <*> parseJSON (indexV ary 4)
                <*> parseJSON (indexV ary 5)
                <*> parseJSON (indexV ary 6)
                <*> parseJSON (indexV ary 7)
    {-# INLINE parseJSON #-}

instance (ToJSON a, ToJSON b, ToJSON c, ToJSON d, ToJSON e, ToJSON f,
          ToJSON g, ToJSON h, ToJSON i) => ToJSON (a,b,c,d,e,f,g,h,i) where
    toJSON (a,b,c,d,e,f,g,h,i) = arrayValue $ arrayValueList
      [ toJSON a, toJSON b, toJSON c, toJSON d
      , toJSON e, toJSON f, toJSON g, toJSON h
      , toJSON i]
    {-# INLINE toJSON #-}

instance (FromJSON a, FromJSON b, FromJSON c, FromJSON d, FromJSON e,
          FromJSON f, FromJSON g, FromJSON h, FromJSON i) =>
         FromJSON (a,b,c,d,e,f,g,h,i) where
    parseJSON = withArray "(a,b,c,d,e,f,g,h,i)" $ \ary ->
        let n = JSA.length ary
        in if n /= 9
           then fail $ "cannot unpack array of length " ++
                       show n ++ " into a 9-tuple"
           else (,,,,,,,,)
                <$> parseJSON (indexV ary 0)
                <*> parseJSON (indexV ary 1)
                <*> parseJSON (indexV ary 2)
                <*> parseJSON (indexV ary 3)
                <*> parseJSON (indexV ary 4)
                <*> parseJSON (indexV ary 5)
                <*> parseJSON (indexV ary 6)
                <*> parseJSON (indexV ary 7)
                <*> parseJSON (indexV ary 8)
    {-# INLINE parseJSON #-}

instance (ToJSON a, ToJSON b, ToJSON c, ToJSON d, ToJSON e, ToJSON f,
          ToJSON g, ToJSON h, ToJSON i, ToJSON j) =>
         ToJSON (a,b,c,d,e,f,g,h,i,j) where
    toJSON (a,b,c,d,e,f,g,h,i,j) = arrayValue $ arrayValueList
      [ toJSON a, toJSON b, toJSON c, toJSON d
      , toJSON e, toJSON f, toJSON g, toJSON h
      , toJSON i, toJSON j]
    {-# INLINE toJSON #-}

instance (FromJSON a, FromJSON b, FromJSON c, FromJSON d, FromJSON e,
          FromJSON f, FromJSON g, FromJSON h, FromJSON i, FromJSON j) =>
         FromJSON (a,b,c,d,e,f,g,h,i,j) where
    parseJSON = withArray "(a,b,c,d,e,f,g,h,i,j)" $ \ary ->
        let n = JSA.length ary
        in if n /= 10
           then fail $ "cannot unpack array of length " ++
                       show n ++ " into a 10-tuple"
           else (,,,,,,,,,)
                <$> parseJSON (indexV ary 0)
                <*> parseJSON (indexV ary 1)
                <*> parseJSON (indexV ary 2)
                <*> parseJSON (indexV ary 3)
                <*> parseJSON (indexV ary 4)
                <*> parseJSON (indexV ary 5)
                <*> parseJSON (indexV ary 6)
                <*> parseJSON (indexV ary 7)
                <*> parseJSON (indexV ary 8)
                <*> parseJSON (indexV ary 9)
    {-# INLINE parseJSON #-}

instance (ToJSON a, ToJSON b, ToJSON c, ToJSON d, ToJSON e, ToJSON f,
          ToJSON g, ToJSON h, ToJSON i, ToJSON j, ToJSON k) =>
         ToJSON (a,b,c,d,e,f,g,h,i,j,k) where
    toJSON (a,b,c,d,e,f,g,h,i,j,k) = arrayValue $ arrayValueList
      [ toJSON a, toJSON b, toJSON c, toJSON d
      , toJSON e, toJSON f, toJSON g, toJSON h
      , toJSON i, toJSON j, toJSON k]
    {-# INLINE toJSON #-}

instance (FromJSON a, FromJSON b, FromJSON c, FromJSON d, FromJSON e,
          FromJSON f, FromJSON g, FromJSON h, FromJSON i, FromJSON j,
          FromJSON k) =>
         FromJSON (a,b,c,d,e,f,g,h,i,j,k) where
    parseJSON = withArray "(a,b,c,d,e,f,g,h,i,j,k)" $ \ary ->
        let n = JSA.length ary
        in if n /= 11
           then fail $ "cannot unpack array of length " ++
                       show n ++ " into an 11-tuple"
           else (,,,,,,,,,,)
                <$> parseJSON (indexV ary 0)
                <*> parseJSON (indexV ary 1)
                <*> parseJSON (indexV ary 2)
                <*> parseJSON (indexV ary 3)
                <*> parseJSON (indexV ary 4)
                <*> parseJSON (indexV ary 5)
                <*> parseJSON (indexV ary 6)
                <*> parseJSON (indexV ary 7)
                <*> parseJSON (indexV ary 8)
                <*> parseJSON (indexV ary 9)
                <*> parseJSON (indexV ary 10)
    {-# INLINE parseJSON #-}

instance (ToJSON a, ToJSON b, ToJSON c, ToJSON d, ToJSON e, ToJSON f,
          ToJSON g, ToJSON h, ToJSON i, ToJSON j, ToJSON k, ToJSON l) =>
         ToJSON (a,b,c,d,e,f,g,h,i,j,k,l) where
    toJSON (a,b,c,d,e,f,g,h,i,j,k,l) = arrayValue $ arrayValueList
      [ toJSON a, toJSON b, toJSON c, toJSON d
      , toJSON e, toJSON f, toJSON g, toJSON h
      , toJSON i, toJSON j, toJSON k, toJSON l]
    {-# INLINE toJSON #-}

instance (FromJSON a, FromJSON b, FromJSON c, FromJSON d, FromJSON e,
          FromJSON f, FromJSON g, FromJSON h, FromJSON i, FromJSON j,
          FromJSON k, FromJSON l) =>
         FromJSON (a,b,c,d,e,f,g,h,i,j,k,l) where
    parseJSON = withArray "(a,b,c,d,e,f,g,h,i,j,k,l)" $ \ary ->
        let n = JSA.length ary
        in if n /= 12
           then fail $ "cannot unpack array of length " ++
                       show n ++ " into a 12-tuple"
           else (,,,,,,,,,,,)
                <$> parseJSON (indexV ary 0)
                <*> parseJSON (indexV ary 1)
                <*> parseJSON (indexV ary 2)
                <*> parseJSON (indexV ary 3)
                <*> parseJSON (indexV ary 4)
                <*> parseJSON (indexV ary 5)
                <*> parseJSON (indexV ary 6)
                <*> parseJSON (indexV ary 7)
                <*> parseJSON (indexV ary 8)
                <*> parseJSON (indexV ary 9)
                <*> parseJSON (indexV ary 10)
                <*> parseJSON (indexV ary 11)
    {-# INLINE parseJSON #-}

instance (ToJSON a, ToJSON b, ToJSON c, ToJSON d, ToJSON e, ToJSON f,
          ToJSON g, ToJSON h, ToJSON i, ToJSON j, ToJSON k, ToJSON l,
          ToJSON m) =>
         ToJSON (a,b,c,d,e,f,g,h,i,j,k,l,m) where
    toJSON (a,b,c,d,e,f,g,h,i,j,k,l,m) = arrayValue $ arrayValueList
      [ toJSON a, toJSON b, toJSON c, toJSON d
      , toJSON e, toJSON f, toJSON g, toJSON h
      , toJSON i, toJSON j, toJSON k, toJSON l
      , toJSON m]
    {-# INLINE toJSON #-}

instance (FromJSON a, FromJSON b, FromJSON c, FromJSON d, FromJSON e,
          FromJSON f, FromJSON g, FromJSON h, FromJSON i, FromJSON j,
          FromJSON k, FromJSON l, FromJSON m) =>
         FromJSON (a,b,c,d,e,f,g,h,i,j,k,l,m) where
    parseJSON = withArray "(a,b,c,d,e,f,g,h,i,j,k,l,m)" $ \ary ->
        let n = JSA.length ary
        in if n /= 13
           then fail $ "cannot unpack array of length " ++
                       show n ++ " into a 13-tuple"
           else (,,,,,,,,,,,,)
                <$> parseJSON (indexV ary 0)
                <*> parseJSON (indexV ary 1)
                <*> parseJSON (indexV ary 2)
                <*> parseJSON (indexV ary 3)
                <*> parseJSON (indexV ary 4)
                <*> parseJSON (indexV ary 5)
                <*> parseJSON (indexV ary 6)
                <*> parseJSON (indexV ary 7)
                <*> parseJSON (indexV ary 8)
                <*> parseJSON (indexV ary 9)
                <*> parseJSON (indexV ary 10)
                <*> parseJSON (indexV ary 11)
                <*> parseJSON (indexV ary 12)
    {-# INLINE parseJSON #-}

instance (ToJSON a, ToJSON b, ToJSON c, ToJSON d, ToJSON e, ToJSON f,
          ToJSON g, ToJSON h, ToJSON i, ToJSON j, ToJSON k, ToJSON l,
          ToJSON m, ToJSON n) =>
         ToJSON (a,b,c,d,e,f,g,h,i,j,k,l,m,n) where
    toJSON (a,b,c,d,e,f,g,h,i,j,k,l,m,n) = arrayValue $ arrayValueList
      [ toJSON a, toJSON b, toJSON c, toJSON d
      , toJSON e, toJSON f, toJSON g, toJSON h
      , toJSON i, toJSON j, toJSON k, toJSON l
      , toJSON m, toJSON n]
    {-# INLINE toJSON #-}

instance (FromJSON a, FromJSON b, FromJSON c, FromJSON d, FromJSON e,
          FromJSON f, FromJSON g, FromJSON h, FromJSON i, FromJSON j,
          FromJSON k, FromJSON l, FromJSON m, FromJSON n) =>
         FromJSON (a,b,c,d,e,f,g,h,i,j,k,l,m,n) where
    parseJSON = withArray "(a,b,c,d,e,f,g,h,i,j,k,l,m,n)" $ \ary ->
        let n = JSA.length ary
        in if n /= 14
           then fail $ "cannot unpack array of length " ++
                       show n ++ " into a 14-tuple"
           else (,,,,,,,,,,,,,)
                <$> parseJSON (indexV ary 0)
                <*> parseJSON (indexV ary 1)
                <*> parseJSON (indexV ary 2)
                <*> parseJSON (indexV ary 3)
                <*> parseJSON (indexV ary 4)
                <*> parseJSON (indexV ary 5)
                <*> parseJSON (indexV ary 6)
                <*> parseJSON (indexV ary 7)
                <*> parseJSON (indexV ary 8)
                <*> parseJSON (indexV ary 9)
                <*> parseJSON (indexV ary 10)
                <*> parseJSON (indexV ary 11)
                <*> parseJSON (indexV ary 12)
                <*> parseJSON (indexV ary 13)
    {-# INLINE parseJSON #-}

instance (ToJSON a, ToJSON b, ToJSON c, ToJSON d, ToJSON e, ToJSON f,
          ToJSON g, ToJSON h, ToJSON i, ToJSON j, ToJSON k, ToJSON l,
          ToJSON m, ToJSON n, ToJSON o) =>
         ToJSON (a,b,c,d,e,f,g,h,i,j,k,l,m,n,o) where
    toJSON (a,b,c,d,e,f,g,h,i,j,k,l,m,n,o) = arrayValue $ arrayValueList
      [ toJSON a, toJSON b, toJSON c, toJSON d
      , toJSON e, toJSON f, toJSON g, toJSON h
      , toJSON i, toJSON j, toJSON k, toJSON l
      , toJSON m, toJSON n, toJSON o]
    {-# INLINE toJSON #-}

instance (FromJSON a, FromJSON b, FromJSON c, FromJSON d, FromJSON e,
          FromJSON f, FromJSON g, FromJSON h, FromJSON i, FromJSON j,
          FromJSON k, FromJSON l, FromJSON m, FromJSON n, FromJSON o) =>
         FromJSON (a,b,c,d,e,f,g,h,i,j,k,l,m,n,o) where
    parseJSON = withArray "(a,b,c,d,e,f,g,h,i,j,k,l,m,n,o)" $ \ary ->
        let n = JSA.length ary
        in if n /= 15
           then fail $ "cannot unpack array of length " ++
                       show n ++ " into a 15-tuple"
           else (,,,,,,,,,,,,,,)
                <$> parseJSON (indexV ary 0)
                <*> parseJSON (indexV ary 1)
                <*> parseJSON (indexV ary 2)
                <*> parseJSON (indexV ary 3)
                <*> parseJSON (indexV ary 4)
                <*> parseJSON (indexV ary 5)
                <*> parseJSON (indexV ary 6)
                <*> parseJSON (indexV ary 7)
                <*> parseJSON (indexV ary 8)
                <*> parseJSON (indexV ary 9)
                <*> parseJSON (indexV ary 10)
                <*> parseJSON (indexV ary 11)
                <*> parseJSON (indexV ary 12)
                <*> parseJSON (indexV ary 13)
                <*> parseJSON (indexV ary 14)
    {-# INLINE parseJSON #-}

instance ToJSON a => ToJSON (Dual a) where
    toJSON = toJSON . getDual
    {-# INLINE toJSON #-}

instance FromJSON a => FromJSON (Dual a) where
    parseJSON = fmap Dual . parseJSON
    {-# INLINE parseJSON #-}

instance ToJSON a => ToJSON (First a) where
    toJSON = toJSON . getFirst
    {-# INLINE toJSON #-}

instance FromJSON a => FromJSON (First a) where
    parseJSON = fmap First . parseJSON
    {-# INLINE parseJSON #-}

instance ToJSON a => ToJSON (Last a) where
    toJSON = toJSON . getLast
    {-# INLINE toJSON #-}

instance FromJSON a => FromJSON (Last a) where
    parseJSON = fmap Last . parseJSON
    {-# INLINE parseJSON #-}

-- | @withObject expected f value@ applies @f@ to the 'Object' when @value@ is an @Object@
--   and fails using @'typeMismatch' expected@ otherwise.
withObject :: String -> (Object -> Parser a) -> Value -> Parser a
withObject _        f (match -> Object obj) = f obj
withObject expected _ v                     = typeMismatch expected v
{-# INLINE withObject #-}

{-
-- | @withText expected f value@ applies @f@ to the 'Text' when @value@ is a @String@
--   and fails using @'typeMismatch' expected@ otherwise.
withText :: String -> (Text -> Parser a) -> Value -> Parser a
withText _        f (String txt) = f txt
withText expected _ v            = typeMismatch expected v
{-# INLINE withText #-}
-}

withJSString :: String -> (JSString -> Parser a) -> Value -> Parser a
withJSString _        f (match -> String txt) = f txt
withJSString expected _ v                     = typeMismatch expected v
{-# INLINE withJSString #-}

-- | @withArray expected f value@ applies @f@ to the 'Array' when @value@ is an @Array@
--   and fails using @'typeMismatch' expected@ otherwise.
withArray :: String -> (JSArray -> Parser a) -> Value -> Parser a
withArray _        f (match -> Array arr) = f arr
withArray expected _ v                    = typeMismatch expected v
{-# INLINE withArray #-}

{-
-- | @withNumber expected f value@ applies @f@ to the 'Number' when @value@ is a 'Number'.
--   and fails using @'typeMismatch' expected@ otherwise.
withNumber :: String -> (Number -> Parser a) -> Value -> Parser a
withNumber expected f = withScientific expected (f . scientificToNumber)
{-# INLINE withNumber #-}
{-# DEPRECATED withNumber "Use withScientific instead" #-}
-}
-- | @withScientific expected f value@ applies @f@ to the 'Double' number when @value@ is a 'Number'.
--   and fails using @'typeMismatch' expected@ otherwise.
withDouble :: String -> (Double -> Parser a) -> Value -> Parser a
withDouble _        f (match -> Number d) = f d
withDouble expected _ v          = typeMismatch expected v
{-# INLINE withDouble #-}

-- | @withBool expected f value@ applies @f@ to the 'Bool' when @value@ is a @Bool@
--   and fails using @'typeMismatch' expected@ otherwise.
withBool :: String -> (Bool -> Parser a) -> Value -> Parser a
withBool _        f (match -> Bool arr) = f arr
withBool expected _ v                   = typeMismatch expected v
{-# INLINE withBool #-}

-- | Construct a 'Pair' from a key and a value.
(.=) :: ToJSON a => JSString -> a -> Pair
name .= value = (name, toJSON value)
{-# INLINE (.=) #-}

-- | Convert a value from JSON, failing if the types do not match.
fromJSON :: (FromJSON a) => Value -> Result a
fromJSON = parse parseJSON
{-# INLINE fromJSON #-}

-- | Retrieve the value associated with the given key of an 'Object'.
-- The result is 'empty' if the key is not present or the value cannot
-- be converted to the desired type.
--
-- This accessor is appropriate if the key and value /must/ be present
-- in an object for it to be valid.  If the key and value are
-- optional, use '(.:?)' instead.
(.:) :: (FromJSON a) => Object -> JSString -> Parser a
obj .: key = case I.lookup key obj of
               Nothing -> fail $ "key " ++ show key ++ " not present"
               Just v  -> parseJSON v
{-# INLINE (.:) #-}

-- | Retrieve the value associated with the given key of an 'Object'.
-- The result is 'Nothing' if the key is not present, or 'empty' if
-- the value cannot be converted to the desired type.
--
-- This accessor is most useful if the key and value can be absent
-- from an object without affecting its validity.  If the key and
-- value are mandatory, use '(.:)' instead.
(.:?) :: (FromJSON a) => Object -> JSString -> Parser (Maybe a)
obj .:? key = case I.lookup key obj of
               Nothing -> pure Nothing
               Just v  -> parseJSON v
{-# INLINE (.:?) #-}

-- | Helper for use in combination with '.:?' to provide default
-- values for optional JSON object fields.
--
-- This combinator is most useful if the key and value can be absent
-- from an object without affecting its validity and we know a default
-- value to assign in that case.  If the key and value are mandatory,
-- use '(.:)' instead.
--
-- Example usage:
--
-- @ v1 <- o '.:?' \"opt_field_with_dfl\" .!= \"default_val\"
-- v2 <- o '.:'  \"mandatory_field\"
-- v3 <- o '.:?' \"opt_field2\"
-- @
(.!=) :: Parser (Maybe a) -> a -> Parser a
pmval .!= val = fromMaybe val <$> pmval
{-# INLINE (.!=) #-}

-- | Fail parsing due to a type mismatch, with a descriptive message.
typeMismatch :: String -- ^ The name of the type you are trying to parse.
             -> Value  -- ^ The actual value encountered.
             -> Parser a
typeMismatch expected actual =
    fail $ "when expecting a " ++ expected ++ ", encountered " ++ name ++
           " instead"
  where
    name = case match actual of
             Object _ -> "Object"
             Array _  -> "Array"
             String _ -> "String"
             Number _ -> "Number"
             Bool _   -> "Boolean"
             Null     -> "Null"

realFloatToJSON :: RealFloat a => a -> Value
realFloatToJSON d
    | isNaN d || isInfinite d = nullValue
    | otherwise               = doubleValue (realToFrac d)
{-# INLINE realFloatToJSON #-}

scientificToNumber :: Scientific -> Number
scientificToNumber s
    | e < 0     = D $ Scientific.toRealFloat s
    | otherwise = I $ c * 10 ^ e
  where
    e = Scientific.base10Exponent s
    c = Scientific.coefficient s
{-# INLINE scientificToNumber #-}

parseRealFloat :: RealFloat a => String -> Value -> Parser a
parseRealFloat _        (match -> Number d) = pure $ realToFrac d
parseRealFloat _        (match -> Null)     = pure (0/0)
parseRealFloat expected v                   = typeMismatch expected v
{-# INLINE parseRealFloat #-}

parseIntegral :: Integral a => String -> Value -> Parser a
parseIntegral expected = withDouble expected $ pure . floor
{-# INLINE parseIntegral #-}

arrayToValueList :: JSArray -> [Value]
arrayToValueList x = unsafeCoerce (JSA.toList x) -- fixme should me normal coerce
{-# INLINE arrayToValueList #-}
