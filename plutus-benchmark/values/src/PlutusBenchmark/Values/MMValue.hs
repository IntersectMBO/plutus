module PlutusBenchmark.Values.MMValue (
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
import Data.Function (on)
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as HM
import Data.Monoid (Sum (..))
import Data.MonoidMap (MonoidMap)
import Data.MonoidMap qualified as MM

newtype Value = Value
    { getValue :: MonoidMap ByteString (MonoidMap ByteString (Sum Integer))
    }
    deriving stock (Show, Eq)
    deriving newtype (Semigroup, Monoid)
    deriving newtype (NFData)

toHMap :: Value -> Map ByteString (Map ByteString Integer)
toHMap = MM.toMap . MM.map (HM.map getSum . MM.toMap) . getValue

empty :: Value
empty = mempty

insertCoin :: ByteString -> ByteString -> Integer -> Value -> Value
insertCoin currencyName coinName amount =
    Value
    . MM.append (MM.singleton currencyName (MM.singleton coinName (Sum amount)))
    . getValue

lookupCoin :: ByteString -> ByteString -> Value -> Sum Integer
lookupCoin currencyName coinName =
    MM.get coinName
    . MM.get currencyName
    . getValue

deleteCoin :: ByteString -> ByteString -> Value -> Value
deleteCoin currencyName coinName =
    Value
    . MM.adjust (MM.nullify coinName) currencyName
    . getValue

union :: Value -> Value -> Value
union = (<>)

valueContains :: Value -> Value -> Bool
valueContains (Value m1) (Value m2) =
    MM.isSubmapOfBy (MM.isSubmapOfBy ((<=) `on` getSum)) m2 m1

byPolicyId :: ByteString -> Value -> MonoidMap ByteString (Sum Integer)
byPolicyId policyId (Value m) =
    MM.get policyId m

byTokenName :: ByteString -> Value -> MonoidMap ByteString (Sum Integer)
byTokenName tokenName (Value m) =
    MM.foldMapWithKey' (\policyId innerMM ->
        MM.singleton policyId (MM.get tokenName innerMM)
        )
        m
