
module Language.Marlowe.ACTUS.Model.Utility.ANN.Annuity
  (annuity)
where

import           Data.List                  (foldl', tails)
import           Language.Marlowe.ACTUS.Ops (ActusNum (..), ActusOps (..))
import           Prelude                    hiding (Fractional, Num, (*), (+), (-), (/))

-- |annuity amount function (A), as described in section 3.8 in the
-- ACTUS reference v1.1
annuity :: (ActusOps a, ActusNum a) =>
     a   -- ^ actual interest rate
  -> [a] -- ^ ti
  -> a
annuity r ti = numerator / denominator

  where
    numerator   = _product $ map ((+_one).(*r)) ti
    denominator = _sum (map _product $ tails $ map ((+_one).(*r)) ti)

    -- note that _product [] == 1
    _product :: (ActusNum a, ActusOps a) => [a] -> a
    _product = foldl' (*) _one

    _sum :: (ActusNum a, ActusOps a) => [a] -> a
    _sum = foldl' (+) _zero
