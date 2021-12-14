-- |
-- Module      : Foundation.Format.CSV.Types
-- License     : BSD-style
-- Maintainer  : Foundation
-- Stability   : experimental
-- Portability : portable
--

{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE OverloadedStrings          #-}
{-# LANGUAGE FlexibleInstances          #-}

module Foundation.Format.CSV.Types
    (-- * CSV
      CSV
    , unCSV

    -- * Row
    , Row
    , unRow
    , Record(..)
    -- * Field
    , Field(..)
    , Escaping(..)
    , IsField(..)
    -- ** helpers
    , integral
    , float
    , string
    ) where

import           Basement.Imports
import           Basement.BoxedArray              (Array, length, unsafeIndex)
import           Basement.NormalForm              (NormalForm(..))
import           Basement.From                    (Into, into)
import           Basement.String                  (String, any, elem, null, uncons)
import qualified Basement.String       as String (singleton)
import           Basement.Types.Word128           (Word128)
import           Basement.Types.Word256           (Word256)
import           Basement.Types.OffsetSize        (Offset, CountOf)
import           Foundation.Collection.Element    (Element)
import           Foundation.Collection.Collection (Collection, nonEmpty_)
import           Foundation.Collection.Sequential (Sequential)
import           Foundation.Collection.Indexed    (IndexedCollection)
import           Foundation.Check.Arbitrary       (Arbitrary(..), frequency)
import           Foundation.String.Read (readDouble, readInteger)

-- | CSV field
data Field
    = FieldInteger Integer
    | FieldDouble  Double
    | FieldString  String  Escaping
  deriving (Eq, Show, Typeable)
instance NormalForm Field where
    toNormalForm (FieldInteger i) = toNormalForm i
    toNormalForm (FieldDouble  d) = toNormalForm d
    toNormalForm (FieldString  s e) = toNormalForm s `seq` toNormalForm e
instance Arbitrary Field where
    arbitrary = frequency $ nonEmpty_ [ (1, FieldInteger <$> arbitrary)
                                      , (1, FieldDouble <$> arbitrary)
                                      , (3, string <$> arbitrary)
                                      ]

data Escaping = NoEscape | Escape | DoubleEscape
  deriving (Eq, Ord, Enum, Bounded, Show, Typeable)
instance NormalForm Escaping where
    toNormalForm !_ = ()

class IsField a where
    toField :: a -> Field
    fromField :: Field -> Either String a
instance IsField Field where
    toField = id
    fromField = pure
instance IsField a => IsField (Maybe a) where
    toField Nothing  = FieldString mempty NoEscape
    toField (Just a) = toField a
    fromField stuff@(FieldString p NoEscape)
        | null p = pure Nothing
        | otherwise = Just <$> fromField stuff
    fromField stuff = Just <$> fromField stuff

fromIntegralField :: Integral b => Field -> Either String b
fromIntegralField (FieldString str NoEscape) = case readInteger str of
    Nothing -> Left "Invalid integral field"
    Just v  -> pure $ fromInteger v
fromIntegralField (FieldInteger v) = pure (fromInteger v)
fromIntegralField _ = Left "Expected integral value"

fromDoubleField :: Field -> Either String Double
fromDoubleField (FieldString str NoEscape) = case readDouble str of
    Nothing -> Left "Invalid double field"
    Just v  -> pure v
fromDoubleField (FieldDouble v) = pure v
fromDoubleField _ = Left "Expected double value"

instance IsField Bool where
    toField = toField . show
    fromField (FieldString "True" NoEscape) = pure True
    fromField (FieldString "False" NoEscape) = pure False
    fromField _ = Left "not a boolean value"
instance IsField Int8 where
    toField = FieldInteger . into
    fromField = fromIntegralField
instance IsField Int16 where
    toField = FieldInteger . into
    fromField = fromIntegralField
instance IsField Int32 where
    toField = FieldInteger . into
    fromField = fromIntegralField
instance IsField Int64 where
    toField = FieldInteger . into
    fromField = fromIntegralField
instance IsField Int where
    toField = FieldInteger . into
    fromField = fromIntegralField

instance IsField Word8 where
    toField = FieldInteger . into
    fromField = fromIntegralField
instance IsField Word16 where
    toField = FieldInteger . into
    fromField = fromIntegralField
instance IsField Word32 where
    toField = FieldInteger . into
    fromField = fromIntegralField
instance IsField Word64 where
    toField = FieldInteger . into
    fromField = fromIntegralField
instance IsField Word where
    toField = FieldInteger . into
    fromField = fromIntegralField
instance IsField Word128 where
    toField = FieldInteger . into
    fromField = fromIntegralField
instance IsField Word256 where
    toField = FieldInteger . into
    fromField = fromIntegralField

instance IsField Integer where
    toField = FieldInteger
    fromField = fromIntegralField
instance IsField Natural where
    toField = FieldInteger . into
    fromField = fromIntegralField

instance IsField Double where
    toField = FieldDouble
    fromField = fromDoubleField

instance IsField Char where
    toField = string . String.singleton
    fromField (FieldString str _) = case uncons str of
        Just (c, str') | null str' -> pure c
                       | otherwise -> Left "Expected a char, but received a String"
        Nothing -> Left "Expected a char"
    fromField _ = Left "Expected a char"

instance IsField (Offset a) where
    toField = FieldInteger . into
    fromField = fromIntegralField
instance IsField (CountOf a) where
    toField = FieldInteger . into
    fromField = fromIntegralField

instance IsField [Char] where
    toField = string . fromString
    fromField (FieldString str _) = pure $ toList str
    fromField _ = Left "Expected a Lazy String"
instance IsField String where
    toField = string
    fromField (FieldString str _) = pure str
    fromField _ = Left "Expected a UTF8 String"

-- | helper function to create a `FieldInteger`
--
integral :: Into Integer a => a -> Field
integral = FieldInteger . into

float :: Double -> Field
float = FieldDouble

-- | heler function to create a FieldString.
--
-- This function will findout automatically if an escaping is needed.
-- if you wish to perform the escaping manually, do not used this function
--
string :: String -> Field
string s = FieldString s encoding
  where
    encoding
        | any g s   = DoubleEscape
        | any f s   = Escape
        | otherwise = NoEscape
    g c = c == '\"'
    f c = c `elem` ",\r\n"

-- | CSV Row
--
newtype Row = Row { unRow :: Array Field }
  deriving (Eq, Show, Typeable, Semigroup, Monoid, Collection, NormalForm, Sequential, IndexedCollection)

type instance Element Row = Field
instance IsList Row where
    type Item Row = Field
    toList = toList . unRow
    fromList = Row . fromList

class Record a where
    toRow :: a -> Row
    fromRow :: Row -> Either String a
instance Record Row where
    toRow = id
    fromRow = pure
instance (IsField a, IsField b) => Record (a,b) where
    toRow (a,b) = fromList [toField a, toField b]
    fromRow (Row row)
        | length row == 2 = (,) <$> fromField (row `unsafeIndex` 0) <*> fromField (row `unsafeIndex` 1)
        | otherwise       = Left (show row)
instance (IsField a, IsField b, IsField c) => Record (a,b,c) where
    toRow (a,b,c) = fromList [toField a, toField b, toField c]
    fromRow (Row row)
        | length row == 3 = (,,) <$> fromField (row `unsafeIndex` 0)
                                 <*> fromField (row `unsafeIndex` 1)
                                 <*> fromField (row `unsafeIndex` 2)
        | otherwise       = Left (show row)
instance (IsField a, IsField b, IsField c, IsField d) => Record (a,b,c,d) where
    toRow (a,b,c,d) = fromList [toField a, toField b, toField c, toField d]
    fromRow (Row row)
        | length row == 4 = (,,,) <$> fromField (row `unsafeIndex` 0)
                                  <*> fromField (row `unsafeIndex` 1)
                                  <*> fromField (row `unsafeIndex` 2)
                                  <*> fromField (row `unsafeIndex` 3)
        | otherwise       = Left (show row)
instance (IsField a, IsField b, IsField c, IsField d, IsField e) => Record (a,b,c,d,e) where
    toRow (a,b,c,d,e) = fromList [toField a, toField b, toField c, toField d, toField e]
    fromRow (Row row)
        | length row == 5 = (,,,,) <$> fromField (row `unsafeIndex` 0)
                                   <*> fromField (row `unsafeIndex` 1)
                                   <*> fromField (row `unsafeIndex` 2)
                                   <*> fromField (row `unsafeIndex` 3)
                                   <*> fromField (row `unsafeIndex` 4)
        | otherwise       = Left (show row)
instance (IsField a, IsField b, IsField c, IsField d, IsField e, IsField f) => Record (a,b,c,d,e,f) where
    toRow (a,b,c,d,e,f) = fromList [toField a, toField b, toField c, toField d, toField e, toField f]
    fromRow (Row row)
        | length row == 6 = (,,,,,) <$> fromField (row `unsafeIndex` 0)
                                    <*> fromField (row `unsafeIndex` 1)
                                    <*> fromField (row `unsafeIndex` 2)
                                    <*> fromField (row `unsafeIndex` 3)
                                    <*> fromField (row `unsafeIndex` 4)
                                    <*> fromField (row `unsafeIndex` 5)
        | otherwise       = Left (show row)

-- | CSV Type
newtype CSV = CSV { unCSV :: Array Row }
  deriving (Eq, Show, Typeable, Semigroup, Monoid, Collection, NormalForm, Sequential, IndexedCollection)

type instance Element CSV = Row

instance IsList CSV where
    type Item CSV = Row
    toList = toList . unCSV
    fromList = CSV . fromList
