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
import Data.Map.Merge.Strict qualified as Map
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
insertCoin currencyName coinName amount =
    Value
    . Map.update
        (\innerMap ->
            let newInner =
                    if amount == 0
                    then Map.delete coinName innerMap
                    else Map.insert coinName amount innerMap
             in if Map.null newInner
                then Nothing
                else Just newInner
        )
        currencyName
    . getValue

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
union (Value m1) (Value m2) =
    Value
    $ Map.merge
        Map.preserveMissing
        Map.preserveMissing
        (Map.zipWithMaybeMatched
            (\_ innerMap1 innerMap2 ->
                let mergedInner =
                        Map.merge
                            Map.preserveMissing
                            Map.preserveMissing
                            (Map.zipWithMaybeMatched
                                (\_ v1 v2 ->
                                    if v1 + v2 == 0
                                    then Nothing
                                    else Just (v1 + v2)
                                )
                            )
                            innerMap1
                            innerMap2
                 in if Map.null mergedInner
                    then Nothing
                    else Just mergedInner
            )
        )
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
