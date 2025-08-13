module PlutusBenchmark.Values.NestedValue (
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
    { getValue :: Map ByteString (Map ByteString Integer)
    }
    deriving stock (Show, Eq)
    deriving newtype (NFData)

toHMap :: Value -> Map ByteString (Map ByteString Integer)
toHMap = getValue

empty :: Value
empty = Value Map.empty

insertCoin :: ByteString -> ByteString -> Integer -> Value -> Value
insertCoin currencyName coinName amount (Value m) =
    normalize insertCoin'
  where
    insertCoin' =
        Value
        $ Map.adjust
            (Map.insert coinName amount)
            currencyName
            m

lookupCoin :: ByteString -> ByteString -> Value -> Integer
lookupCoin currencyName coinName  =
    Map.findWithDefault 0 coinName
    . Map.findWithDefault Map.empty currencyName
    . getValue

deleteCoin :: ByteString -> ByteString -> Value -> Value
deleteCoin currencyName coinName (Value m) =
    Value
    $ Map.update
        (\innerMap ->
            let innerMap' = Map.delete coinName innerMap
            in if Map.null innerMap'
                then Nothing
                else Just innerMap'
        )
        currencyName
        m

union :: Value -> Value -> Value
union (Value m1) (Value m2) = normalize union'
  where
    union' =
        Value
        $ Map.unionWith
            (Map.unionWith (+))
            m1
            m2

valueContains :: Value -> Value -> Bool
valueContains (Value m1) (Value m2) =
    Map.isSubmapOfBy (Map.isSubmapOfBy (<=)) m2 m1

byPolicyId :: ByteString -> Value -> Map ByteString Integer
byPolicyId policyId (Value m) =
    Map.findWithDefault Map.empty policyId m

byTokenName :: ByteString -> Value -> Map ByteString Integer
byTokenName tokenName (Value m) =
    Map.foldrWithKey'
        (\policyId innerMap acc ->
            case Map.lookup tokenName innerMap of
                Just amount -> Map.insert policyId amount acc
                Nothing     -> acc
        )
        Map.empty
        m

normalize :: Value -> Value
normalize (Value m) =
    Value
    $ Map.filter (not . Map.null)
    $ Map.map (Map.filter (/= 0)) m
