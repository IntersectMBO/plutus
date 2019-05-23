{-# LANGUAGE DeriveAnyClass       #-}
{-# LANGUAGE DeriveGeneric        #-}
{-# LANGUAGE DerivingStrategies   #-}
{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE MonoLocalBinds       #-}
{-# LANGUAGE TemplateHaskell      #-}
{-# LANGUAGE UndecidableInstances #-}
-- | A type for intervals and associated functions.
module Ledger.Interval(
      Interval(..)
    , interval
    , from
    , to
    , always
    , hull
    , intersection
    , overlaps
    ) where

import           Codec.Serialise.Class        (Serialise)
import           Data.Aeson                   (FromJSON, ToJSON)
import           Data.Hashable                (Hashable)
import           Data.Maybe                   (isNothing)
import           Data.Semigroup               (Max (..), Min (..), Option (..), Semigroup ((<>)))
import           Data.Swagger.Internal.Schema (ToSchema)
import           GHC.Generics                 (Generic)

import           Language.PlutusTx.Lift       (makeLift)

-- | An interval of @a@s. The interval is closed below and open above, meaning
--   that @Interval (Just (10 :: Int)) (Just 11)@ contains a single value @11@.
--   The interval is unbounded on either side: @Interval Nothing (Just 12)@
--   contains all numbers smaller than @12@.
data Interval a = Interval { ivFrom :: Maybe a, ivTo :: Maybe a }
    deriving (Eq, Ord, Show)
    deriving stock (Generic)
    deriving anyclass (ToSchema, FromJSON, ToJSON, Serialise, Hashable)

makeLift ''Interval

-- | Check whether a value is covered by an interval.
member :: (a -> a -> Ordering) -> a -> Interval a -> Bool
member comp a i =
    let lw = case ivFrom i of { Nothing -> True; Just f' -> comp f' a /= GT }
        hg = case ivTo i of { Nothing -> True; Just t' -> comp t' a == GT }
    in lw && hg

-- | Check whether two intervals overlap, that is, whether there is a value that
--   is a member of both intervals.
overlaps :: (a -> a -> Ordering) -> Interval a -> Interval a -> Bool
overlaps comp l r =
    let inLow a i = case a of
            Nothing -> isNothing (ivFrom i)
            Just a' -> member comp a' i
    in
        inLow (ivFrom l) r || inLow (ivFrom r) l

-- | 'intersection a b' is the largest interval that is contained in 'a' and in
--   'b', if it exists.
intersection :: Ord a => Interval a -> Interval a -> Maybe (Interval a)
intersection l r =
    if not (overlaps compare l r)
    then Nothing
    else Just (Interval fr t) where
            fr = fmap getMax $ getOption $ (Max <$> Option (ivFrom l)) <> (Max <$> Option (ivFrom r))
            t  = fmap getMin $ getOption $ (Min <$> Option (ivTo l)) <> (Min <$> Option (ivTo r))

-- | 'hull a b' is the smallest interval containing 'a' and 'b'.
hull :: Ord a => Interval a -> Interval a -> Interval a
hull l r = Interval fr t where
        fr = fmap getMin $ (Min <$> ivFrom l) <> (Min <$> ivFrom r)
        t = fmap getMax $ (Max <$> ivTo l) <> (Max <$> ivTo r)

{- note [Definition of Interval]

The purpose of this module is to provide an interval data type that
can be used in on-chain and off-chain code alike. Its two main uses in the
'plutus-wallet-api' module are the validity range of transactions, and the ranges of
funds and slot numbers for wallet triggers.

To ensure that 'Interval' can be used in on-chain code, the functions in this
module do not use type classes or functions from the Haskell Prelude. There are
query functions specialized to 'Interval Slot' exported from 'Ledger.Slot'.
-}

-- | An 'Interval' that covers every slot.
always :: Interval a
always = Interval Nothing Nothing

-- | @from a@ is an 'Interval' that includes all values that are
--  greater than or equal to @a@.
from :: a -> Interval a
from s = Interval (Just s) Nothing

-- | @to a@ is an 'Interval' that includes all values that are
--  smaller than @a@.
to :: a -> Interval a
to s = Interval Nothing (Just s)

-- | @interval a b@ includes all values that are greater than or equal
--   to @a@ and smaller than @b@. Therefore it includes @a@ but not it
--   does not include @b@.
interval :: a -> a -> Interval a
interval s s' = Interval (Just s) (Just s')
