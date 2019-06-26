{-# LANGUAGE AllowAmbiguousTypes        #-}
{-# LANGUAGE DefaultSignatures          #-}
{-# LANGUAGE DeriveAnyClass             #-}
{-# LANGUAGE DeriveGeneric              #-}
{-# LANGUAGE DerivingStrategies         #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE OverloadedStrings          #-}
{-# LANGUAGE RecordWildCards            #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE TypeApplications           #-}
{-# LANGUAGE TypeFamilies               #-}
{-# LANGUAGE TypeOperators              #-}
{-# LANGUAGE TypeSynonymInstances       #-}

module Schema
    ( ToSchema
    , toSchema
    , TypeSignature(..)
    , toTypeSignature
    , typeSignature
    , DataType(..)
    , Constructor(..)
    , ConstructorName(..)
    ) where

import           Control.Newtype.Generics (Newtype)
import           Data.Aeson               (FromJSON, ToJSON)
import           Data.Map                 (Map)
import           Data.Monoid              ((<>))
import           Data.Proxy               (Proxy (Proxy))
import           Data.String              (IsString)
import           Data.Text                (Text)
import qualified Data.Text                as Text
import           Data.Typeable            (splitTyConApp)
import           GHC.Generics             ((:*:) ((:*:)), (:+:), C1, D1, Generic, M1 (M1), Rec0, Rep, S1, Selector, U1,
                                           V1, conIsRecord, conName, from, selName)
import qualified GHC.Generics             as GHC
import           Type.Reflection          (SomeTypeRep, Typeable, someTypeRep, tyConModule, tyConName)

{-# ANN module ("HLint: ignore Avoid restricted function" :: Text)
        #-}

data TypeSignature =
    TypeSignature
        { moduleName         :: Text
        , constructorName    :: Text
        , argumentSignatures :: [TypeSignature]
        }
    deriving (Eq, Show, Ord, Generic)
    deriving anyclass (ToJSON, FromJSON)

data DataType =
    DataType TypeSignature [Constructor]
    deriving (Eq, Show, Generic)
    deriving anyclass (ToJSON, FromJSON)

data Constructor
    = Constructor ConstructorName [DataType]
    | Record ConstructorName [(Text, DataType)]
    deriving (Eq, Show, Generic)
    deriving anyclass (ToJSON, FromJSON)

newtype ConstructorName =
    ConstructorName Text
    deriving (Eq, Show, Generic)
    deriving anyclass (FromJSON, ToJSON, Newtype)
    deriving newtype (IsString)

------------------------------------------------------------
asPrimitive ::
       forall a. Typeable a
    => DataType
asPrimitive = DataType (typeSignature @a) []

typeSignature ::
       forall a. Typeable a
    => TypeSignature
typeSignature = fromTypeRep $ someTypeRep (Proxy @a)
  where
    fromTypeRep :: SomeTypeRep -> TypeSignature
    fromTypeRep rep = postProcess TypeSignature {..}
      where
        (constructor, arguments) = splitTyConApp rep
        moduleName = Text.pack $ tyConModule constructor
        constructorName = Text.pack $ tyConName constructor
        argumentSignatures = fromTypeRep <$> arguments
        -- We'll do a little post-processing to tidy up `[Char] => String`.
        postProcess :: TypeSignature -> TypeSignature
        postProcess TypeSignature { moduleName = "GHC.Types"
                                  , constructorName = "[]"
                                  , argumentSignatures = [TypeSignature { moduleName = "GHC.Types"
                                                                        , constructorName = "Char"
                                                                        , argumentSignatures = []
                                                                        }]
                                  } =
            TypeSignature
                { moduleName = "GHC.Types"
                , constructorName = "String"
                , argumentSignatures = []
                }
        postProcess x = x

toTypeSignature :: DataType -> TypeSignature
toTypeSignature (DataType sig _) = sig

------------------------------------------------------------
class ToSchema a where
    toSchema :: DataType
    default toSchema :: (Generic a, Typeable a, GenericToSchema (Rep a)) =>
        DataType
    toSchema =
        DataType (typeSignature @a) . genericToSchema $ from (undefined :: a)

instance ToSchema Bool where
    toSchema = asPrimitive @Bool

instance ToSchema Int where
    toSchema = asPrimitive @Int

instance ToSchema Integer where
    toSchema = asPrimitive @Integer

instance ToSchema Text where
    toSchema = asPrimitive @Text

instance ToSchema a => ToSchema (Proxy a) where
    toSchema = toSchema @a

instance (Typeable a, Typeable b, ToSchema a, ToSchema b) =>
         ToSchema (a, b) where
    toSchema =
        DataType
            (typeSignature @(a, b))
            [Constructor (ConstructorName "Tuple") [toSchema @a, toSchema @b]]

instance (Typeable k, Typeable v) => ToSchema (Map k v) where
    toSchema = asPrimitive @(Map k v)

instance (Typeable a) => ToSchema [a] where
    toSchema = asPrimitive @[a]

------------------------------------------------------------
class GenericToSchema f where
    genericToSchema :: f a -> [Constructor]

instance GenericToSchema (D1 i V1) where
    genericToSchema _ = []

instance (GenericToConstructors f) => GenericToSchema (D1 i f) where
    genericToSchema (M1 constructors) = genericToConstructors constructors

instance (Typeable a, ToSchema a) => ToSchema (Maybe a)

------------------------------------------------------------
class GenericToConstructors f where
    genericToConstructors :: f a -> [Constructor]

instance (GenericToConstructors f, GenericToConstructors g) =>
         GenericToConstructors (f :+: g) where
    genericToConstructors _ =
        genericToConstructors (undefined :: f a) <>
        genericToConstructors (undefined :: g a)

instance (GHC.Constructor i, GenericToFields f) =>
         GenericToConstructors (C1 i f) where
    genericToConstructors constructor@(M1 selectors)
      -- Unfortunately, GHC Generics doesn't make a _type-level_
      -- distinction between record selectors and product
      -- selectors. So there's no way to know at compile time if a
      -- selector is a named record field or an unnamed product field.
      --
      -- The best we can do is trust that conIsRecord will deliver
      -- either only named fields or only unnamed ones.
     =
        pure $
        if conIsRecord constructor
            then Record name (onlyPairs fields)
            else Constructor name (excludePairs fields)
      where
        name = ConstructorName $ Text.pack $ conName constructor
        fields = genericToFields selectors

onlyPairs ::
       (Applicative f, Foldable f, Monoid (f (a, b)))
    => f (Maybe a, b)
    -> f (a, b)
onlyPairs = foldMap f
  where
    f (Nothing, _) = mempty
    f (Just a, b)  = pure (a, b)

excludePairs ::
       (Applicative f, Foldable f, Monoid (f b)) => f (Maybe a, b) -> f b
excludePairs = foldMap f
  where
    f (Nothing, b) = pure b
    f (Just _, _)  = mempty

------------------------------------------------------------
class GenericToFields f where
    genericToFields :: f a -> [(Maybe Text, DataType)]

instance GenericToFields U1 where
    genericToFields _ = []

instance (GenericToFields f, GenericToFields g) =>
         GenericToFields (f :*: g) where
    genericToFields ~(f :*: g) = genericToFields f <> genericToFields g

instance (ToSchema f, Selector s) => GenericToFields (S1 s (Rec0 f)) where
    genericToFields selector =
        case selName selector of
            ""   -> [(Nothing, reference)]
            name -> [(Just (Text.pack name), reference)]
      where
        reference = toSchema @f
