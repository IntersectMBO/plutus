module PlutusBenchmark.Values.FlattenedValue (
    Value (..),
    insertCoin,
    lookupCoin,
    deleteCoin,
    union,
    valueContains,
    byPolicyId,
    byTokenName,
    empty,
    toHMap,
) where

import Control.DeepSeq (NFData)
import Data.ByteString (ByteString)
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map

newtype Value = Value
    { getValue :: Map (ByteString, ByteString) Integer
    }
    deriving stock (Show, Eq)
    deriving newtype (NFData)

toHMap :: Value -> Map ByteString (Map ByteString Integer)
toHMap = Map.foldrWithKey' (\(p, t) i acc -> Map.insertWith Map.union p (Map.singleton t i) acc) Map.empty . getValue

empty :: Value
empty = Value Map.empty

insertCoin :: ByteString -> ByteString -> Integer -> Value -> Value
insertCoin currencyName coinName amount (Value m) =
    normalize insertCoin'
  where
    insertCoin' =
        Value
        $ Map.insertWith (+) (currencyName, coinName) amount m

lookupCoin :: ByteString -> ByteString -> Value -> Maybe Integer
lookupCoin currencyName coinName (Value m) =
    Map.lookup (currencyName, coinName) m

deleteCoin :: ByteString -> ByteString -> Value -> Value
deleteCoin currencyName coinName (Value m) =
    Value $ Map.delete (currencyName, coinName) m

union :: Value -> Value -> Value
union (Value m1) (Value m2) =
    normalize union'
  where
    union' =
        Value $ Map.unionWith (+) m1 m2

valueContains :: Value -> Value -> Bool
valueContains (Value m1) (Value m2) =
    Map.isSubmapOfBy (<=) m2 m1

byPolicyId :: ByteString -> Value -> Map ByteString Integer
byPolicyId policyId (Value m) =
    Map.foldrWithKey'
        (\(pId, tn) amount acc ->
            if pId == policyId
                then Map.insert tn amount acc
                else acc
        )
        Map.empty
        m

byTokenName :: ByteString -> Value -> Map ByteString Integer
byTokenName tokenName (Value m) =
    Map.foldrWithKey'
        (\(pId, tn) amount acc ->
            if tn == tokenName
                then Map.insert pId amount acc
                else acc
        )
        Map.empty
        m

normalize :: Value -> Value
normalize (Value m) =
    Value $ Map.filter (/= 0) m

-- {}
-- {k1 -> 2, k2 -> 3}
-- {k4 -> 2}
