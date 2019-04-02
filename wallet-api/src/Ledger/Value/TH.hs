{-# LANGUAGE DeriveAnyClass     #-}
{-# LANGUAGE DeriveGeneric      #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE TemplateHaskell    #-}
{-# LANGUAGE LambdaCase         #-}
module Ledger.Value.TH(
      Value(..)
    , CurrencySymbol
    , currencySymbol
    , singleton
    , valueOf
    , scale
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
import           Data.Aeson                   (FromJSON, ToJSON)
import           Data.Swagger.Internal.Schema (ToSchema)
import           GHC.Generics                 (Generic)
import           Language.PlutusTx.Lift       (makeLift)
import qualified Language.PlutusTx.Prelude    as P
import           Language.Haskell.TH          (Q, TExp)
import           Prelude                      hiding (all, lookup, negate)

data CurrencySymbol = CurrencySymbol Int
  deriving (Eq, Ord, Show)
  deriving stock (Generic)
  deriving anyclass (ToSchema, ToJSON, FromJSON, Serialise)

makeLift ''CurrencySymbol

currencySymbol :: Q (TExp (Int -> CurrencySymbol))
currencySymbol = [|| CurrencySymbol ||]

-- | Cryptocurrency value
--   See note [Currencies]
newtype Value = Value { getValue :: [(CurrencySymbol, Int)] }
    deriving (Show)
    deriving stock (Generic)
    deriving anyclass (ToSchema, ToJSON, FromJSON)
    deriving newtype (Serialise)

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

type CurrencyMap v = [(CurrencySymbol, v)]

cmap :: Q (TExp ((v -> w) -> CurrencyMap v -> CurrencyMap w))
cmap = [||
    \f ->
        let go [] = []
            go ((c, i):xs') = (c, f i) : go xs'
        in go
    ||]

lookup :: Q (TExp (CurrencySymbol -> CurrencyMap v -> Maybe v))
lookup = [||
    \(CurrencySymbol cur) xs ->
        let
            go :: [(CurrencySymbol, v)] -> Maybe v
            go []                          = Nothing
            go ((CurrencySymbol c, i):xs') = if $$(P.eq) c cur then Just i else go xs'
        in go xs
 ||]

-- | How much of a given currency is in a 'Value'
valueOf :: Q (TExp (Value -> CurrencySymbol -> Int))
valueOf = [||
  \(Value xs) cur ->
      case $$(lookup) cur xs of
        Nothing -> 0 :: Int
        Just i  -> i
   ||]

data These a b = This a | That b | These a b

these :: Q (TExp (a -> b -> (a -> b -> c) -> These a b -> c))
these = [||
    \a' b' f -> \case
        This a -> f a b'
        That b -> f a' b
        These a b -> f a b
    ||]

union :: Q (TExp (CurrencyMap a -> CurrencyMap b -> CurrencyMap (These a b)))
union = [||
    \ls rs ->
        let
            f a b' = case b' of
                Nothing -> This a
                Just b  -> These a b
            ls' = $$(P.map) (\(c, i) -> (c, (f i ($$(lookup) c rs)))) ls
            rs' = $$(P.filter) (\(CurrencySymbol c, _) -> $$(P.not) ($$(P.any) (\(CurrencySymbol c', _) -> $$(P.eq) c' c) ls)) rs
            rs'' = $$(P.map) (\(c, b) -> (c, (That b))) rs'
        in $$(P.append) ls' rs''
  ||]

singleton :: Q (TExp (CurrencySymbol -> Int -> Value))
singleton = [|| \c i -> Value [(c, i)] ||]

unionWith :: Q (TExp ((Int -> Int -> Int) -> Value -> Value -> Value))
unionWith = [||
  \f (Value ls) (Value rs) ->
    let
        combined = $$(union) ls rs
        unThese k = case k of
            This a    -> f a 0
            That b    -> f 0 b
            These a b -> f a b
    in Value ($$(cmap) unThese combined)
  ||]

all :: Q (TExp ((v -> Bool) -> CurrencyMap v -> Bool))
all = [|| \p -> let go xs = case xs of { [] -> True; (_, x):xs' -> $$(P.and) (p x) (go xs') } in go ||]

scale :: Q (TExp (Int -> Value -> Value))
scale = [|| \i (Value xs) -> Value ($$(P.map) (\(c, i') -> (c, $$(P.multiply) i i')) xs) ||]

-- Num operations

plus :: Q (TExp (Value -> Value -> Value))
plus = [|| $$(unionWith) $$(P.plus) ||]

negate :: Q (TExp (Value -> Value))
negate = [|| $$(scale) (-1) ||]

minus :: Q (TExp (Value -> Value -> Value))
minus = [|| $$(unionWith) $$(P.minus) ||]

multiply :: Q (TExp (Value -> Value -> Value))
multiply = [|| $$(unionWith) $$(P.multiply) ||]

zero :: Q (TExp Value)
zero = [|| Value [] ||]

isZero :: Q (TExp (Value -> Bool))
isZero = [|| \(Value xs) -> $$(P.all) (\(_, i) -> $$(P.eq) 0 i) xs ||]

geq :: Q (TExp (Value -> Value -> Bool))
geq = [||
  \(Value ls) (Value rs) ->
    let
        p = $$(these) 0 0 $$(P.geq)
    in
      $$(all) p ($$(union) ls rs) ||]

gt :: Q (TExp (Value -> Value -> Bool))
gt = [||
    \(Value ls) (Value rs) ->
    let
        p = $$(these) 0 0 $$(P.gt)
    in
        $$(all) p ($$(union) ls rs) ||]

leq :: Q (TExp (Value -> Value -> Bool))
leq = [||
    \(Value ls) (Value rs) ->
    let
        p = $$(these) 0 0 $$(P.leq)
    in
        $$(all) p ($$(union) ls rs) ||]

lt :: Q (TExp (Value -> Value -> Bool))
lt = [||
    \(Value ls) (Value rs) ->
        let
            p = $$(these) 0 0 $$(P.lt)
        in
        $$(all) p ($$(union) ls rs) ||]

eq :: Q (TExp (Value -> Value -> Bool))
eq = [||
    \(Value ls) (Value rs) ->
    let
        p = $$(these) 0 0 $$(P.eq)
    in
        $$(all) p ($$(union) ls rs) ||]
