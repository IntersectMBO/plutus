{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DefaultSignatures   #-}
{-# LANGUAGE DeriveAnyClass      #-}
{-# LANGUAGE DeriveGeneric       #-}
{-# LANGUAGE DerivingStrategies  #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE FlexibleInstances   #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeFamilies        #-}
{-# LANGUAGE TypeOperators       #-}

module Schema
    ( ToSchema
    , toSchema
    , FormSchema(..)
    ) where

import           Data.Aeson   (FromJSON, ToJSON)
import           Data.Monoid  ((<>))
import           Data.Proxy   (Proxy)
import           Data.Text    (Text)
import           GHC.Generics ((:*:) ((:*:)), (:+:), C1, Constructor, D1, Generic, M1 (M1), Rec0, Rep, S1, Selector, U1,
                               conIsRecord, conName, from, selName)

{-# ANN module ("HLint: ignore Avoid restricted function" :: Text)
        #-}

data FormSchema
    = FormSchemaUnit
    | FormSchemaBool
    | FormSchemaInt
    | FormSchemaString
    | FormSchemaHex
    | FormSchemaArray FormSchema
    | FormSchemaMaybe FormSchema
    | FormSchemaRadio [String]
    | FormSchemaTuple FormSchema FormSchema
    | FormSchemaObject [(String, FormSchema)]
    -- Blessed types that get their own special UI widget.
    | FormSchemaValue
    | FormSchemaSlotRange
    -- Exceptions.
    | FormSchemaUnsupported
          { description :: String
          }
    deriving (Show, Eq, Generic)
    deriving anyclass (FromJSON, ToJSON)

------------------------------------------------------------
class ToSchema a where
    toSchema :: FormSchema
    default toSchema :: (Generic a, GenericToSchema (Rep a)) =>
        FormSchema
    toSchema = genericToSchema $ from (undefined :: a)

instance ToSchema () where
    toSchema = FormSchemaUnit

instance ToSchema Bool where
    toSchema = FormSchemaBool

instance ToSchema Int where
    toSchema = FormSchemaInt

instance ToSchema Integer where
    toSchema = FormSchemaInt

instance ToSchema Text where
    toSchema = FormSchemaString

instance ToSchema a => ToSchema (Proxy a) where
    toSchema = toSchema @a

instance (ToSchema a, ToSchema b) => ToSchema (a, b) where
    toSchema = FormSchemaTuple (toSchema @a) (toSchema @b)

instance ToSchema String where
    toSchema = FormSchemaString

instance {-# OVERLAPPABLE #-} (ToSchema a) => ToSchema [a] where
    toSchema = FormSchemaArray (toSchema @a)

-- ------------------------------------------------------------
class GenericToSchema f where
    genericToSchema :: f a -> FormSchema

instance (GenericToSchema f) => GenericToSchema (D1 d f) where
    genericToSchema (M1 constructors) = genericToSchema constructors

instance (Constructor c, GenericToFields f) => GenericToSchema (C1 c f) where
    genericToSchema c@(M1 selectors) =
        if conIsRecord c
            then FormSchemaObject $ genericToFields selectors
            else FormSchemaUnsupported
                     {description = "Unsupported, non-record constructor."}

instance (GenericToConstructorName c1, GenericToConstructorName c2) =>
         GenericToSchema (c1 :+: c2) where
    genericToSchema _ =
        FormSchemaRadio $
        genericToConstructorName (undefined :: c1 a) <>
        genericToConstructorName (undefined :: c2 a)

instance ToSchema a => ToSchema (Maybe a) where
    toSchema = FormSchemaMaybe $ toSchema @a

------------------------------------------------------------
class GenericToConstructorName f where
    genericToConstructorName :: f a -> [String]

instance (Constructor c) => GenericToConstructorName (C1 c U1) where
    genericToConstructorName c = [conName c]

instance (GenericToConstructorName c1, GenericToConstructorName c2) =>
         GenericToConstructorName (c1 :+: c2) where
    genericToConstructorName _ =
        genericToConstructorName (undefined :: c1 a) <>
        genericToConstructorName (undefined :: c2 a)

------------------------------------------------------------
class GenericToFields f where
    genericToFields :: f a -> [(String, FormSchema)]

instance (GenericToFields f, GenericToFields g) =>
         GenericToFields (f :*: g) where
    genericToFields ~(f :*: g) = genericToFields f <> genericToFields g

instance (ToSchema f, Selector s) => GenericToFields (S1 s (Rec0 f)) where
    genericToFields selector = [(selName selector, toSchema @f)]

------------------------------------------------------------
newtype Slot =
    Slot
        { getSlot :: Integer
        }
    deriving (Show, Eq, Ord, Generic)
    deriving anyclass (ToSchema)

newtype CurrencySymbol =
    CurrencySymbol
        { unCurrencySymbol :: Text
        }
    deriving (Show, Eq, Ord, Generic)
    deriving anyclass (ToSchema)

newtype TokenName =
    TokenName
        { unTokenName :: Text
        }
    deriving (Show, Eq, Ord, Generic)
    deriving anyclass (ToSchema)

newtype AssocMap k v =
    AssocMap
        { unMap :: [(k, v)]
        }
    deriving (Show, Eq, Ord, Generic)
    deriving anyclass (ToSchema)

newtype Value =
    Value
        { getValue :: AssocMap CurrencySymbol (AssocMap TokenName Integer)
        }
    deriving (Show, Eq, Ord, Generic)
    deriving anyclass (ToSchema)

data Interval a =
    Interval
        { ivFrom :: Maybe a
        , ivTo   :: Maybe a
        }
    deriving (Show, Eq, Ord, Generic)
    deriving anyclass (ToSchema)

data VestingTranche =
    VestingTranche
        { vestingTrancheDate   :: Slot
        , vestingTrancheAmount :: Value
        , validity             :: Interval Slot
        }
    deriving (Show, Eq, Ord, Generic)
    deriving anyclass (ToSchema)
