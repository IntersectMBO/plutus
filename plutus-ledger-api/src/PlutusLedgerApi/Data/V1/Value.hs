{-# LANGUAGE MultiWayIf        #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE ViewPatterns      #-}

module PlutusLedgerApi.Data.V1.Value where

import PlutusLedgerApi.V1.Value hiding (Value (..))
import PlutusTx qualified
import PlutusTx.Builtins.Internal qualified as BI
import PlutusTx.DataMap (Map)
import PlutusTx.DataMap qualified as Map
import PlutusTx.Prelude as PlutusTx

import Prelude qualified as Haskell

newtype Value = Value {getValue :: Map.Map CurrencySymbol (Map.Map TokenName Integer)}
  deriving stock (Haskell.Show)
  deriving newtype (PlutusTx.ToData, PlutusTx.FromData, PlutusTx.UnsafeFromData)

instance Haskell.Eq Value where
  (==) = eq

instance Eq Value where
  {-# INLINEABLE (==) #-}
  (==) = eq

{-# INLINEABLE unordEqWith #-}

{- | Check equality of two lists given a function checking whether a 'Value' is zero and a function
checking equality of values.

This function recurses on both the lists in parallel and checks whether the key-value pairs are
equal pointwise. If there is a mismatch, then it tries to find the left key-value pair in the right
list. If that succeeds then the pair is removed from both the lists and recursion proceeds pointwise
as before until there's another mismatch. If at some point a key-value pair from the left list is
not found in the right one, then the function returns 'False'. If the left list is exhausted, but
the right one still has some non-zero elements, the function returns 'False' as well.

We check equality of values of two key-value pairs right after ensuring that the keys match. This is
disadvantageous if the values are big and there's a key that is present in one of the lists but not
in the other, since in that case computing equality of values was expensive and pointless. However

1. we've checked and on the chain 'Value's very rarely contain 'CurrencySymbol's with more than 3
   'TokenName's associated with them, so we optimize for the most common use case
2. computing equality of values before ensuring equality of all the keys certainly does help when we
   check equality of 'TokenName'-value pairs, since the value of a 'TokenName' is an 'Integer' and
   @(==) :: Integer -> Integer -> Bool@ is generally much faster than repeatedly searching for keys
   in a list
3. having some clever logic for computing equality of values right away in some cases, but not in
   others would not only complicate the algorithm, but also increase the size of the function and
   this resource is quite scarce as the size of a program growing beyond what's acceptable by the
   network can be a real deal breaker, while general performance concerns don't seem to be as
   pressing

The algorithm we use here is very similar, if not identical, to @valueEqualsValue4@ from
https://github.com/input-output-hk/plutus/issues/5135
-}
unordEqWith ::
  forall k a.
  ( PlutusTx.Eq k
  , PlutusTx.UnsafeFromData k
  , PlutusTx.UnsafeFromData a
  , PlutusTx.ToData k
  , PlutusTx.ToData a
  ) =>
  (a -> Bool) ->
  (a -> a -> Bool) ->
  Map k a ->
  Map k a ->
  Bool
unordEqWith is0 eqV = goBoth
  where
    -- Recurse on the spines of both the lists simultaneously.
    goBoth kvsL kvsR
      -- One spine is longer than the other one, but this still can result in a
      -- succeeding equality.
      -- check if the non-empty list only contains zero values.
      | Map.null kvsL = Map.all is0 kvsR
      -- Symmetric to the previous case.
      | Map.null kvsR = Map.all is0 kvsL
      -- Both spines are non-empty.
      | otherwise =
          let ((kL, vL), kvsL') = Map.unsafeUncons kvsL
              (kvR0@(kR0, vR0), kvsR0') = Map.unsafeUncons kvsR
           in if
                -- We could've avoided having this clause if we always searched for the
                -- right key-value pair using @goRight@, however the sheer act of invoking
                -- that function, passing an empty list to it as an accumulator and calling
                -- 'revAppend' afterwards affects performance quite a bit, considering that
                -- all of that happens for every single element of the left list.
                -- Hence we handle the special case of lists being equal pointwise (or at
                -- least their prefixes being equal pointwise) with a bit of additional logic
                -- to get some easy -- performance gains.
                | kL == kR0 -> if vL `eqV` vR0 then goBoth kvsL' kvsR0' else False
                | is0 vL -> goBoth kvsL' kvsR
                | otherwise ->
                    let reassemble :: [(k, a)] -> Map k a -> Map k a
                        reassemble [] m = m
                        reassemble ((k, a) : xs) m =
                          let tl = Map.toBuiltinList m
                              hd =
                                BI.mkPairData
                                  (PlutusTx.toBuiltinData k)
                                  (PlutusTx.toBuiltinData a)
                           in reassemble xs (Map.unsafeFromBuiltinList (BI.mkCons hd tl))

                        -- Recurse on the spine of the right list looking for a key-value
                        -- pair whose key matches @kL@, i.e. the first key in the remaining
                        -- part of the left list. The accumulator contains (in reverse order)
                        -- all elements of the right list processed so far whose keys are not
                        -- equal to @kL@ and values are non-zero.
                        goRight :: [(k, a)] -> Map k a -> Bool
                        goRight acc kvsR1'
                          | Map.null kvsR1' = False
                          | otherwise =
                              let (kvR@(kR, vR), kvsR') = Map.unsafeUncons kvsR1'
                               in if kL == kR
                                    then
                                      if vL `eqV` vR
                                        then goBoth kvsL' (reassemble acc kvsR')
                                        else False
                                    else goRight (kvR : acc) kvsR'
                     in goRight [kvR0 | not (is0 vR0)] kvsR0'

{-# INLINEABLE eq #-}

{- | Check equality of two 'Value's. Does not assume orderness of lists within a 'Value' or a lack
of empty values (such as a token whose quantity is zero or a currency that has a bunch of such
tokens or no tokens at all), but does assume that no currencies or tokens within a single
currency have multiple entries.
-}
eq :: Value -> Value -> Bool
eq (Value currs1) (Value currs2) =
  unordEqWith (Map.all (0 ==)) (unordEqWith (0 ==) (==)) currs1 currs2
