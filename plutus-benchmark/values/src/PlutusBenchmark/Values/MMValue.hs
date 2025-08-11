module PlutusBenchmark.Values.MMValue where

import Control.DeepSeq (NFData)
import Data.ByteString (ByteString)
import Data.Monoid (Sum (..))
import Data.MonoidMap (MonoidMap)
import Data.MonoidMap qualified as MM

newtype Value = Value
    { getValue :: MonoidMap ByteString (MonoidMap ByteString (Sum Integer))
    }
    deriving stock (Show, Eq)
    deriving newtype (Semigroup, Monoid)
    deriving newtype (NFData)

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
    MM.isSubmapOf m2 m1

byPolicyId :: ByteString -> Value -> MonoidMap ByteString (Sum Integer)
byPolicyId policyId (Value m) =
    MM.get policyId m

byTokenName :: ByteString -> Value -> MonoidMap ByteString (Sum Integer)
byTokenName tokenName (Value m) =
    MM.foldMapWithKey' (\policyId innerMM ->
        MM.singleton policyId (MM.get tokenName innerMM)
        )
        m

type Test = MonoidMap String (Sum Integer)

ex1 :: Test
ex1 = mempty

ex2 :: Test
ex2 = MM.set "foo" 1 ex1

ex3 :: Test
ex3 = MM.set "foo" 100 ex2

ex4 :: Test
ex4 = MM.append ex2 ex3
