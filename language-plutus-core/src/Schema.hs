{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE DefaultSignatures     #-}
{-# LANGUAGE DeriveAnyClass        #-}
{-# LANGUAGE DerivingStrategies    #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE TypeSynonymInstances  #-}
{-# LANGUAGE UndecidableInstances  #-}

module Schema
    ( SimpleArgumentSchema(..)
    , toSchema
    , ToSchema
    ) where

import           Data.Aeson   (FromJSON, ToJSON)
import           Data.Monoid  ((<>))
import           Data.Proxy   (Proxy (Proxy))
import           Data.Text    (Text)
import qualified Data.Text    as Text
import           GHC.Generics ((:*:), C1, Constructor, D1, Generic, Rec0, Rep, S1, Selector, conIsRecord, conName, from,
                               selName, unM1)

data SimpleArgumentSchema
    = SimpleIntSchema
    | SimpleStringSchema
    | SimpleHexSchema
    | SimpleArraySchema SimpleArgumentSchema
    | SimpleTupleSchema (SimpleArgumentSchema, SimpleArgumentSchema)
    | SimpleObjectSchema [(Text, SimpleArgumentSchema)]
    | ValueSchema [(Text, SimpleArgumentSchema)]
    | UnknownSchema Text Text
    deriving (Eq, Ord, Show)
    deriving (Generic)
    deriving anyclass (FromJSON, ToJSON)

class ToSchema a where
    toSchema :: a -> SimpleArgumentSchema
    default toSchema :: (Generic a, GenericToSchema (Rep a)) =>
        a -> SimpleArgumentSchema
    toSchema = genericToSchema . from

instance (ToSchema a, ToSchema b) => ToSchema (a, b) where
    toSchema _ =
        SimpleTupleSchema
            (toSchema (Proxy :: Proxy a), toSchema (Proxy :: Proxy b))

instance ToSchema Int where
    toSchema _ = SimpleIntSchema

instance ToSchema Integer where
    toSchema _ = SimpleIntSchema

instance ToSchema (Maybe a) where
    toSchema _ = UnknownSchema "Maybe" "We don't currently support this type."

instance ToSchema Text where
    toSchema _ = SimpleStringSchema

instance (ToSchema a) => ToSchema (Proxy a) where
    toSchema _ = toSchema (undefined :: a)

------------------------------------------------------------
-- This is a type family trick that allows us to implement a dedicated
-- instance for `String` (ie. `[Char]`) while still having a more
-- general implementation for any other kind of `[a]`,
--
-- See: https://kseo.github.io/posts/2017-02-05-avoid-overlapping-instances-with-closed-type-families.html
type family (IsSpecialListElement a) :: Bool where
    IsSpecialListElement Char = 'True
    IsSpecialListElement a = 'False

class ListToSchema (flag :: Bool) a where
    listToSchema :: Proxy flag -> [a] -> SimpleArgumentSchema

instance ListToSchema 'True Char where
    listToSchema _ _ = SimpleStringSchema

instance ToSchema a => ListToSchema 'False a where
    listToSchema _ _ = SimpleArraySchema $ toSchema (Proxy :: Proxy a)

instance (IsSpecialListElement a ~ flag, ListToSchema flag a) =>
         ToSchema [a] where
    toSchema = listToSchema (Proxy :: Proxy flag)

------------------------------------------------------------
class GenericToSchema f where
    genericToSchema :: f a -> SimpleArgumentSchema

instance (GenericToSchema f) => GenericToSchema (D1 d f) where
    genericToSchema d = genericToSchema $ unM1 d

instance (Constructor c, GenericSchemaField f) => GenericToSchema (C1 c f) where
    genericToSchema c =
        if conIsRecord c
            then SimpleObjectSchema fields
            else UnknownSchema
                     name
                     "We don't currently support non-record constructors"
      where
        name = Text.pack $ conName c
        fields = genericToSchemaField $ unM1 c

class GenericSchemaField f where
    genericToSchemaField :: f a -> [(Text, SimpleArgumentSchema)]

instance ToSchema a => GenericToSchema (Rec0 a) where
    genericToSchema _ = toSchema (Proxy :: Proxy a)

instance (Selector s, GenericToSchema a) => GenericSchemaField (S1 s a) where
    genericToSchemaField selector =
        [(Text.pack (selName selector), genericToSchema (undefined :: a p))]

instance (GenericSchemaField f, GenericSchemaField g) =>
         GenericSchemaField (f :*: g) where
    genericToSchemaField _ =
        genericToSchemaField (undefined :: f p) <>
        genericToSchemaField (undefined :: g p)
