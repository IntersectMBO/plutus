{-# LANGUAGE OverloadedLists #-}
{-# LANGUAGE OverloadedStrings  #-}
{-# LANGUAGE DerivingVia        #-}
{-# LANGUAGE DeriveAnyClass     #-}
{-# LANGUAGE DataKinds          #-}
{-# LANGUAGE DeriveGeneric      #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE TemplateHaskell    #-}
{-# LANGUAGE LambdaCase         #-}
{-# LANGUAGE TypeApplications   #-}
{-# OPTIONS_GHC -O0             #-}
-- | Functions for working with 'Value' in Template Haskell.
module Ledger.Value.TH(
    -- ** Currency symbols
      CurrencySymbol(..)
    , currencySymbol
    , eqCurSymbol
    -- ** Token names
    , TokenName(..)
    , tokenName
    , eqTokenName
    , toString
    -- ** Value
    , Value(..)
    , singleton
    , valueOf
    , scale
    , symbols
      -- * Constants
    , zero
      -- * Num operations
    , plus
    , minus
    , multiply
    , negate
    , geq
    , gt
    , leq
    , lt
    , eq
      -- * Etc.
    , isZero
    ) where

import           Codec.Serialise.Class        (Serialise)
import           Control.Lens                 (set,(.~))
import           Data.Aeson                   (FromJSON, FromJSONKey, ToJSON, ToJSONKey, (.:))
import qualified Data.Aeson                   as JSON
import qualified Data.Aeson.Extras            as JSON
import qualified Data.ByteString.Lazy         as BSL
import qualified Data.ByteString.Lazy.Char8   as C8
import qualified Data.Swagger.Internal        as S
import           Data.Swagger.Schema          (ToSchema(declareNamedSchema))
import qualified Data.Swagger.Lens            as S
import           Data.Swagger                 (SwaggerType(SwaggerObject), NamedSchema(NamedSchema), declareSchemaRef)
import           Data.Proxy                   (Proxy(Proxy))
import           Data.String                  (IsString(fromString))
import qualified Data.Text                    as Text
import           GHC.Generics                 (Generic)
import qualified Language.PlutusTx.Builtins as Builtins
import           Language.PlutusTx.Lift       (makeLift)
import qualified Language.PlutusTx.Prelude    as P
import           Language.Haskell.TH          (Q, TExp)
import qualified Ledger.Map.TH                as Map
import           Prelude                      hiding (all, lookup, negate)
import           LedgerBytes                  (LedgerBytes(LedgerBytes))
import           Data.Function                ((&))

hexSchema :: S.Schema
hexSchema = mempty & set S.type_ S.SwaggerString & set S.format (Just "hex")

stringSchema :: S.Schema
stringSchema = mempty & set S.type_ S.SwaggerString

newtype CurrencySymbol = CurrencySymbol { unCurrencySymbol :: Builtins.SizedByteString 32 }
    deriving (IsString, Show, ToJSONKey, FromJSONKey, Serialise) via LedgerBytes
    deriving stock (Eq, Ord, Generic)

instance ToSchema CurrencySymbol where
  declareNamedSchema _ = pure $ S.NamedSchema (Just "CurrencySymbol") hexSchema

instance ToJSON CurrencySymbol where
  toJSON currencySymbol =
    JSON.object
      [ ( "unCurrencySymbol"
        , JSON.String .
          JSON.encodeByteString .
          BSL.toStrict . Builtins.unSizedByteString . unCurrencySymbol $
          currencySymbol)
      ]

instance FromJSON CurrencySymbol where
  parseJSON =
    JSON.withObject "CurrencySymbol" $ \object -> do
      raw <- object .: "unCurrencySymbol"
      bytes <- JSON.decodeByteString raw
      pure . CurrencySymbol . Builtins.SizedByteString . BSL.fromStrict $ bytes

makeLift ''CurrencySymbol

eqCurSymbol :: Q (TExp (CurrencySymbol -> CurrencySymbol -> Bool))
eqCurSymbol = [|| \(CurrencySymbol l) (CurrencySymbol r) -> $$(P.equalsByteString) l r ||]

currencySymbol :: Q (TExp (P.ByteString -> CurrencySymbol))
currencySymbol = [|| CurrencySymbol ||]

newtype TokenName = TokenName { unTokenName :: Builtins.SizedByteString 32 }
    deriving (Serialise) via LedgerBytes
    deriving stock (Eq, Ord, Generic)

instance IsString TokenName where
  fromString = TokenName . P.SizedByteString . C8.pack

toString :: TokenName -> String
toString = C8.unpack . Builtins.unSizedByteString . unTokenName

instance Show TokenName where
  show = toString

instance ToSchema TokenName where
    declareNamedSchema _ = pure $ S.NamedSchema (Just "TokenName") stringSchema

instance ToJSON TokenName where
    toJSON tokenName =
        JSON.object
        [ ( "unTokenName", JSON.toJSON $ toString tokenName)]

instance FromJSON TokenName where
    parseJSON =
        JSON.withObject "TokenName" $ \object -> do
        raw <- object .: "unTokenName"
        pure . fromString . Text.unpack $ raw

makeLift ''TokenName

eqTokenName :: Q (TExp (TokenName -> TokenName -> Bool))
eqTokenName = [|| \(TokenName l) (TokenName r) -> $$(P.equalsByteString) l r ||]

tokenName :: Q (TExp (P.ByteString -> TokenName))
tokenName = [|| TokenName ||]

-- | A cryptocurrency value. This is a map from 'CurrencySymbol's to a
-- quantity of that currency.
--
-- Operations on currencies are usually implemented /pointwise/. That is,
-- we apply the operation to the quantities for each currency in turn. So
-- when we add two 'Value's the resulting 'Value' has, for each currency,
-- the sum of the quantities of /that particular/ currency in the argument
-- 'Value'. The effect of this is that the currencies in the 'Value' are "independent",
-- and are operated on separately.
--
-- Whenever we need to get the quantity of a currency in a 'Value' where there
-- is no explicit quantity of that currency in the 'Value', then the quantity is
-- taken to be zero.
--
-- See note [Currencies] for more details.
newtype Value = Value { getValue :: Map.Map CurrencySymbol (Map.Map TokenName Int) }
    deriving (Show)
    deriving stock (Generic)
    deriving anyclass (ToJSON, FromJSON)
    deriving newtype (Serialise)

-- 'InnerMap' exists only to trick swagger's generic deriving mechanism
-- into not looping indefinitely when it encounters a nested map.
newtype InnerMap = InnerMap { unMap :: [(TokenName, Int)] }
    deriving stock (Generic)
    deriving anyclass (ToJSON, FromJSON, ToSchema)

instance ToSchema Value where
    declareNamedSchema _ = do
        mapSchema <- declareSchemaRef (Proxy @(Map.Map CurrencySymbol InnerMap))
        return $ 
                NamedSchema (Just "Value") $ mempty
                    & S.type_ .~ SwaggerObject
                    & S.properties .~ ( [ ("getValue", mapSchema)])
                    & S.required .~ [ "getValue" ]

makeLift ''Value

{- note [Currencies]

The 'Value' type represents a collection of amounts of different currencies.

We can think of 'Value' as a vector space whose dimensions are
currencies. At the moment there is only a single currency (Ada), so 'Value'
contains one-dimensional vectors. When currency-creating transactions are
implemented, this will change and the definition of 'Value' will change to a
'Map Currency Int', effectively a vector with infinitely many dimensions whose
non-zero values are recorded in the map.

To create a value of 'Value', we need to specifiy a currency. This can be done
using 'Ledger.Ada.adaValueOf'. To get the ada dimension of 'Value' we use
'Ledger.Ada.fromValue'. Plutus contract authors will be able to define modules
similar to 'Ledger.Ada' for their own currencies.

-}

-- | Get the quantity of the given currency in the 'Value'.
valueOf :: Q (TExp (Value -> CurrencySymbol -> TokenName -> Int))
valueOf = [||
            let valueOf' :: Value -> CurrencySymbol -> TokenName -> Int
                valueOf' (Value mp) cur tn =
                    case $$(Map.lookup) $$(eqCurSymbol) cur mp of
                        Nothing -> 0 :: Int
                        Just i  -> case $$(Map.lookup) $$(eqTokenName) tn i of
                            Nothing -> 0
                            Just v  -> v
            in valueOf'
   ||]

-- | The list of 'CurrencySymbol's of a 'Value'.
symbols :: Q (TExp (Value -> [CurrencySymbol]))
symbols = [|| 
            let symbols' :: Value -> [CurrencySymbol]
                symbols' (Value mp) = $$(Map.keys) mp
            in symbols' ||]

-- | Make a 'Value' containing only the given quantity of the given currency.
singleton :: Q (TExp (CurrencySymbol -> TokenName -> Int -> Value))
singleton = [|| 
             let singleton' :: CurrencySymbol -> TokenName -> Int -> Value
                 singleton' c tn i = 
                    Value ($$(Map.singleton) c ($$(Map.singleton) tn i)) 
             in singleton'
            ||]

-- | Combine two 'Value' maps 
unionVal :: Q (TExp (Value -> Value -> Map.Map CurrencySymbol (Map.Map TokenName (Map.These Int Int))))
unionVal = [|| 
            let unionVal' :: Value -> Value -> Map.Map CurrencySymbol (Map.Map TokenName (Map.These Int Int))
                unionVal' (Value l) (Value r) = 
                    let 
                        combined = $$(Map.union) $$(eqCurSymbol) l r
                        unThese k = case k of
                            Map.This a    -> $$(Map.map) (Map.This) a
                            Map.That b    -> $$(Map.map) (Map.That) b
                            Map.These a b -> $$(Map.union) $$(eqTokenName) a b
                    in ($$(Map.map) unThese combined)
            in unionVal'

        ||]

unionWith :: Q (TExp ((Int -> Int -> Int) -> Value -> Value -> Value))
unionWith = [||
              let unionWith' :: (Int -> Int -> Int) -> Value -> Value -> Value
                  unionWith' f ls rs =
                    let
                        combined = $$unionVal ls rs
                        unThese k' = case k' of
                            Map.This a -> f a 0
                            Map.That b -> f 0 b
                            Map.These a b -> f a b
                    in Value ($$(Map.map) ($$(Map.map) unThese) combined)
              in unionWith'
  ||]

-- | Multiply all the quantities in the 'Value' by the given scale factor.
scale :: Q (TExp (Int -> Value -> Value))
scale = [|| 
          let scale' :: Int -> Value -> Value
              scale' i (Value xs) =
                Value ($$(Map.map) ($$(Map.map) (\i' -> $$(P.multiply) i i')) xs) 
          in scale' ||]

-- Num operations

-- | Add two 'Value's together. See 'Value' for an explanation of how operations on 'Value's work.
plus :: Q (TExp (Value -> Value -> Value))
plus = [|| $$(unionWith) $$(P.plus) ||]

-- | Negate a 'Value's. See 'Value' for an explanation of how operations on 'Value's work.
negate :: Q (TExp (Value -> Value))
negate = [|| $$(scale) (-1) ||]

-- | Subtract one 'Value' from another. See 'Value' for an explanation of how operations on 'Value's work.
minus :: Q (TExp (Value -> Value -> Value))
minus = [|| $$(unionWith) $$(P.minus) ||]

-- | Multiply two 'Value's together. See 'Value' for an explanation of how operations on 'Value's work.
multiply :: Q (TExp (Value -> Value -> Value))
multiply = [|| $$(unionWith) $$(P.multiply) ||]

-- | The empty 'Value'.
zero :: Q (TExp Value)
zero = [|| Value $$(Map.empty) ||]

-- | Check whether a 'Value' is zero.
isZero :: Q (TExp (Value -> Bool))
isZero = [|| 
          let isZero' :: Value -> Bool
              isZero' (Value xs) = $$(Map.all) ($$(Map.all) (\i -> $$(P.eq) 0 i)) xs 
          in isZero' ||]

checkPred :: Q (TExp ((Map.These Int Int -> Bool) -> Value -> Value -> Bool))
checkPred = [||
    let checkPred' :: (Map.These Int Int -> Bool) -> Value -> Value -> Bool
        checkPred' f l r = 
          let
            inner :: Map.Map TokenName (Map.These Int Int) -> Bool
            inner = ($$(Map.all) f)
          in
            $$(Map.all) inner ($$unionVal l r)
    in checkPred'
     ||]

-- | Check whether a binary relation holds for value pairs of two 'Value' maps,
--   supplying 0 where a key is only present in one of them.
checkBinRel :: Q (TExp ((Int -> Int -> Bool) -> Value -> Value -> Bool))
checkBinRel = [||
    let checkBinRel' :: (Int -> Int -> Bool) -> Value -> Value -> Bool
        checkBinRel' f l r =
            let 
                unThese k' = case k' of
                    Map.This a    -> f a 0
                    Map.That b    -> f 0 b
                    Map.These a b -> f a b
            in $$checkPred unThese l r
    in checkBinRel'
    ||]

-- | Check whether one 'Value' is greater than or equal to another. See 'Value' for an explanation of how operations on 'Value's work.
geq :: Q (TExp (Value -> Value -> Bool))
geq = [|| $$checkBinRel $$(P.geq) ||]

-- | Check whether one 'Value' is strictly greater than another. See 'Value' for an explanation of how operations on 'Value's work.
gt :: Q (TExp (Value -> Value -> Bool))
gt = [|| $$checkBinRel $$(P.gt) ||]

-- | Check whether one 'Value' is less than or equal to another. See 'Value' for an explanation of how operations on 'Value's work.
leq :: Q (TExp (Value -> Value -> Bool))
leq = [|| $$checkBinRel $$(P.leq) ||]

-- | Check whether one 'Value' is strictly less than another. See 'Value' for an explanation of how operations on 'Value's work.
lt :: Q (TExp (Value -> Value -> Bool))
lt = [|| $$checkBinRel $$(P.lt) ||]

-- | Check whether one 'Value' is equal to another. See 'Value' for an explanation of how operations on 'Value's work.
eq :: Q (TExp (Value -> Value -> Bool))
eq = [|| $$checkBinRel $$(P.eq) ||]
