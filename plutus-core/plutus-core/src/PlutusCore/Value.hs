{-# LANGUAGE LambdaCase #-}

module PlutusCore.Value
  ( Value -- Do not expose data constructor
  , K -- Do not expose data constructor
  , k
  , unK
  , maxKeyLen
  , Quantity -- Do not expose data constructor
  , quantity
  , unQuantity
  , zeroQuantity
  , addQuantity
  , negativeAmounts
  , NestedMap
  , unpack
  , pack
  , empty
  , fromList
  , toList
  , toFlatList
  , totalSize
  , maxInnerSize
  , insertCoin
  , deleteCoin
  , scaleValue
  , lookupCoin
  , policies
  , valueContains
  , unionValue
  , valueData
  , valueDataMaxSize
  , unValueData
  , buildValueWith
  ) where

import Control.Monad.Extra ((>=>))
import Data.Bifunctor
import Data.ByteString qualified as B
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map

import PlutusCore.Builtin.Result
import PlutusCore.Data (Data (..))
import PlutusCore.Value.Internal

valueDataMaxSize :: Int
valueDataMaxSize = 40_000

{-| \(O(n)\). Encodes `Value` as `Data`, in the same way as non-builtin @Value@.
This is the denotation of @ValueData@ in Plutus V1, V2 and V3. -}
valueData :: Value -> BuiltinResult Data
valueData v =
  if totalSize v <= valueDataMaxSize
    then pure $ Map . fmap (bimap (B . unK) tokensData) . Map.toList . unpack $ v
    else fail $ "valueData: maximum input size (" ++ show valueDataMaxSize ++ ") exceeded"
  where
    tokensData :: Map K Quantity -> Data
    tokensData = Map . fmap (bimap (B . unK) (I . unQuantity)) . Map.toList
{-# INLINEABLE valueData #-}

{-| \(O(n)\). Decodes `Data` into `Value`.
This is the denotation of @UnValueData@ in Plutus V1, V2 and V3. -}
unValueData :: Data -> BuiltinResult Value
unValueData =
  unMap
    >=> buildValueWith
      "unValueData"
      ( \(cData, tsData) ->
          (,)
            <$> unB cData
            <*> unMap tsData
      )
      (\(tData, qData) -> (,) <$> unB tData <*> unQ qData)
  where
    unB :: Data -> BuiltinResult K
    unB = \case
      B b -> maybe (fail $ "unValueData: invalid key: " <> show (B.unpack b)) pure (k b)
      _ -> fail "unValueData: non-B constructor"
    {-# INLINEABLE unB #-}

    unQ :: Data -> BuiltinResult Quantity
    unQ = \case
      I i
        | Just q <- quantity i -> pure q
        | otherwise -> fail "unValueData: invalid quantity"
      _ -> fail "unValueData: non-I constructor"
    {-# INLINEABLE unQ #-}

    unMap :: Data -> BuiltinResult [(Data, Data)]
    unMap = \case
      Map xs -> pure xs
      _ -> fail "unValueData: non-Map constructor"
{-# INLINEABLE unValueData #-}
