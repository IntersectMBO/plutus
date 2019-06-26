{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE DefaultSignatures     #-}
{-# LANGUAGE DeriveAnyClass        #-}
{-# LANGUAGE DeriveGeneric         #-}
{-# LANGUAGE DerivingStrategies    #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE TypeSynonymInstances  #-}
{-# LANGUAGE UndecidableInstances  #-}

module Schema
    ( ToSchema
    , toSchema
    , ToTypeName
    , toTypeName
    , DataType(..)
    , Constructor(..)
    , ConstructorName(..)
    , TypeName(..)
    , Reference(..)
    ) where

import           Control.Newtype.Generics (Newtype, pack, unpack)
import           Crypto.Hash              (Digest)
import           Data.Aeson               (FromJSON, ToJSON)
import qualified Data.ByteString          as BS
import qualified Data.ByteString.Lazy     as LBS
import           Data.Map                 (Map)
import           Data.Monoid              ((<>))
import           Data.Proxy               (Proxy (Proxy))
import           Data.String              (IsString, fromString)
import           Data.Text                (Text)
import qualified Data.Text                as Text
import           GHC.Generics             ((:*:) ((:*:)), (:+:), C1, D1, Datatype, Generic, K1, M1 (M1), Rep, S1,
                                           Selector, U1, V1, conIsRecord, conName, datatypeName, from, moduleName,
                                           selName)
import qualified GHC.Generics             as GHC

{-# ANN module ("HLint: ignore Avoid restricted function" :: Text) #-}

-- data Type
--     = TaggedProduct [(Name, Type)]
--     | TaggedSum [(Name, Type)]
--     | Fun Type Type
--     | Var Name
--     | App Type Type
-- data Kind
--     = Type
--     | KFun Kind Kind
-- data TyDecl =
--     TyDecl
--         { tyName :: (Name, Kind)
--         , params :: [(Name, Type)]
--         , rhs    :: Type
--         }
-- data ValDecl =
--     ValDecl
--         { valName :: (Name, Type)
--         }
------------------------------------------------------------
data DataType =
    DataType TypeName [Parameter] [Constructor]
    deriving (Eq, Show, Generic)
    deriving anyclass (FromJSON, ToJSON)

data Constructor
    = Constructor ConstructorName [Reference]
    | Record ConstructorName [(Text, Reference)]
    deriving (Eq, Show, Generic)
    deriving anyclass (FromJSON, ToJSON)

------------------------------------------------------------
newtype Reference =
    Reference TypeName
    deriving (Eq, Show, Generic)
    deriving anyclass (FromJSON, ToJSON,Newtype)

instance IsString Reference where
    fromString = Reference . fromString

newtype TypeName =
    TypeName Text
    deriving (Eq, Show, Generic)
    deriving anyclass (FromJSON, ToJSON, Newtype)

instance IsString TypeName where
    fromString = TypeName . Text.pack

newtype Parameter =
    Parameter Text
    deriving (Eq, Show, Generic)
    deriving anyclass (FromJSON, ToJSON, Newtype)

instance IsString Parameter where
    fromString = Parameter . Text.pack

newtype ConstructorName =
    ConstructorName Text
    deriving (Eq, Show, Generic)
    deriving anyclass (FromJSON, ToJSON, Newtype)

instance IsString ConstructorName where
    fromString = ConstructorName . Text.pack

------------------------------------------------------------
class ToTypeName a where
    toTypeName :: a -> TypeName
    default toTypeName :: (Generic a, GenericTypeName (Rep a)) =>
        a -> TypeName
    toTypeName = genericTypeName . from

instance ToTypeName (a, b) where
    toTypeName _ = TypeName "Tuple"

instance ToTypeName a => ToTypeName (Proxy a) where
    toTypeName _ = toTypeName (undefined :: a)

-- instance Datatype i => ToTypeName (D1 i f a) where
--     toTypeName d = TypeName $ Text.pack $ moduleName d <> "." <> datatypeName d
instance ToTypeName Text where
    toTypeName _ = toTypeName (Proxy @String)

instance ToTypeName BS.ByteString where
    toTypeName _ = toTypeName (Proxy @String)

instance ToTypeName LBS.ByteString where
    toTypeName _ = toTypeName (Proxy @String)

instance ToTypeName Char where
    toTypeName _ = TypeName "Char"

instance ToTypeName Int where
    toTypeName _ = TypeName "Int"

instance ToTypeName Integer where
    toTypeName _ = toTypeName (Proxy @Int)

instance ToTypeName Bool where
    toTypeName _ = TypeName "Bool"

instance ToTypeName (Map k v) where
    toTypeName _ = TypeName "Data.Map"

instance ToTypeName (Maybe a) where
    toTypeName _ = TypeName "Maybe"

instance ToTypeName (Digest a) where
    toTypeName _ = TypeName "Crypto.Hash.Digest"

------------------------------------------------------------
class GenericTypeName f where
    genericTypeName :: f a -> TypeName

instance (Datatype i) => GenericTypeName (D1 i f) where
    genericTypeName d =
        TypeName $ Text.pack $ moduleName d <> "." <> datatypeName d

------------------------------------------------------------
class ToSchema a where
    toSchema :: a -> DataType
    default toSchema :: (Generic a, GenericToSchema (Rep a)) =>
        a -> DataType
    toSchema = genericToSchema . from

instance (ToTypeName a, ToSchema a) => ToSchema (Maybe a)

instance ToSchema (Digest a) where
    toSchema p = DataType (toTypeName p) [] []

instance ToSchema Int where
    toSchema p = DataType (toTypeName p) [] []

instance ToSchema Integer where
    toSchema p = DataType (toTypeName p) [] []

instance ToSchema Text where
    toSchema p = DataType (toTypeName p) [] []

instance ToSchema a => ToSchema (Proxy a) where
    toSchema _ = toSchema (undefined :: a)

instance (ToTypeName a, ToTypeName b) => ToSchema (a, b) where
    toSchema p =
        DataType
            (toTypeName p)
            []
            [ Constructor
                  (pack (unpack (toTypeName p)))
                  [ Reference (toTypeName (Proxy @a))
                  , Reference (toTypeName (Proxy @b))
                  ]
            ]

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
    listToSchema :: Proxy flag -> [a] -> DataType

instance ListToSchema 'True Char where
    listToSchema _ _ = DataType (TypeName "String") [] []

instance (ToTypeName a, ToTypeName [a]) => ListToSchema 'False a where
    listToSchema _ _ =
        DataType
            (toTypeName (Proxy :: Proxy [a]))
            []
            [ Constructor
                  (pack (unpack (toTypeName (Proxy :: Proxy [a]))))
                  [Reference (toTypeName (Proxy @a))]
            ]

instance (IsSpecialListElement a ~ flag, ListToSchema flag a) =>
         ToSchema [a] where
    toSchema = listToSchema (Proxy :: Proxy flag)

class ListTypeName (flag :: Bool) a where
    listTypeName :: Proxy flag -> [a] -> TypeName

instance ListTypeName 'True Char where
    listTypeName _ _ = TypeName "String"

instance ListTypeName 'False a where
    listTypeName _ _ = TypeName "List"

instance (IsSpecialListElement a ~ flag, ListTypeName flag a) =>
         ToTypeName [a] where
    toTypeName = listTypeName (Proxy :: Proxy flag)

------------------------------------------------------------
class GenericToSchema f where
    genericToSchema :: f a -> DataType

instance (Datatype i) => GenericToSchema (D1 i V1) where
    genericToSchema d = DataType (genericTypeName d) [] []

instance (Datatype i, GenericToConstructors f) => GenericToSchema (D1 i f) where
    genericToSchema datatype@(M1 constructors) =
        DataType
            (genericTypeName datatype)
            []
            (genericToConstructors constructors)

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
      -- | Unfortunately, GHC Generics doesn't make a _type-level_
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
    genericToFields :: f a -> [(Maybe Text, Reference)]

instance GenericToFields U1 where
    genericToFields _ = []

instance (GenericToFields f, GenericToFields g) =>
         GenericToFields (f :*: g) where
    genericToFields ~(f :*: g) = genericToFields f <> genericToFields g

instance (Selector s, GenericToReference f) => GenericToFields (S1 s f) where
    genericToFields selector@(M1 s) =
        case selName selector of
            ""   -> [(Nothing, reference)]
            name -> [(Just (Text.pack name), reference)]
      where
        reference = genericToReference s

------------------------------------------------------------
class GenericToReference f where
    genericToReference :: f a -> Reference

instance (Datatype i) => GenericToReference (D1 i f) where
    genericToReference d = Reference (genericTypeName d)

instance ToTypeName c => GenericToReference (K1 i c) where
    genericToReference _ = Reference (toTypeName (Proxy @c))
