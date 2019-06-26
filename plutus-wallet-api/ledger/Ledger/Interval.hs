{-# LANGUAGE DeriveAnyClass       #-}
{-# LANGUAGE DeriveGeneric        #-}
{-# LANGUAGE DerivingStrategies   #-}
{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE MonoLocalBinds       #-}
{-# LANGUAGE NoImplicitPrelude    #-}
{-# LANGUAGE TemplateHaskell      #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -fno-omit-interface-pragmas #-}
{-# OPTIONS_GHC -fno-ignore-interface-pragmas #-}
-- | A type for intervals and associated functions.
module Ledger.Interval(
      Interval(..)
    , member
    , interval
    , from
    , to
    , always
    , hull
    , intersection
    , overlaps
    , contains
    , isEmpty
    , before
    , after
    ) where

import           Codec.Serialise.Class        (Serialise)
import           Data.Aeson                   (FromJSON, ToJSON)
import           Data.Hashable                (Hashable)
import           Data.Swagger.Internal.Schema (ToSchema)
import           GHC.Generics                 (Generic)
import qualified Prelude                      as Haskell

import           Language.PlutusTx.Lift       (makeLift)
import           Language.PlutusTx.Prelude

-- | An interval of @a@s. The interval is closed below and open above, meaning
--   that @Interval (Just (10 :: Int)) (Just 11)@ contains a single value @11@.
--   The interval is unbounded on either side: @Interval Nothing (Just 12)@
--   contains all numbers smaller than @12@.
data Interval a = Interval { ivFrom :: Maybe a, ivTo :: Maybe a }
    deriving stock (Haskell.Eq, Haskell.Ord, Show, Generic)
    deriving anyclass (ToSchema, FromJSON, ToJSON, Serialise, Hashable)

makeLift ''Interval

-- | Check whether a value is covered by an interval.
member :: Ord a => a -> Interval a -> Bool
member a i =
    let lw = case ivFrom i of { Nothing -> True; Just f' -> f' <= a }
        hg = case ivTo i of { Nothing -> True; Just t' -> t' > a }
    in lw && hg

-- | Check whether two intervals overlap, that is, whether there is a value that
--   is a member of both intervals.
overlaps :: Ord a => Interval a -> Interval a -> Bool
overlaps l r =
    let inLow a i = case a of
            Nothing -> isNothing (ivFrom i)
            Just a' -> member a' i
    in
        inLow (ivFrom l) r || inLow (ivFrom r) l

-- | 'intersection a b' is the largest interval that is contained in 'a' and in
--   'b', if it exists.
intersection :: Ord a => Interval a -> Interval a -> Maybe (Interval a)
intersection l r =
    if not (overlaps l r)
    then Nothing
    else Just (Interval fr t) where
            fr = fmap getMax $ (Max <$> ivFrom l) <> (Max <$> ivFrom r)
            t  = fmap getMin $ (Min <$> ivTo l) <> (Min <$> ivTo r)

-- | 'hull a b' is the smallest interval containing 'a' and 'b'.
hull :: Ord a => Interval a -> Interval a -> Interval a
hull l r = Interval fr t where
        fr = fmap getMin $ (Min <$> ivFrom l) <> (Min <$> ivFrom r)
        t = fmap getMax $ (Max <$> ivTo l) <> (Max <$> ivTo r)

-- | @a `contains` b@ is true if the 'Interval' @b@ is entirely contained in
--   @a@. That is, @a `contains` b@ if for every entry @s@, if @member s b@ then
--   @member s a@.
contains :: Ord a => Interval a -> Interval a -> Bool
contains (Interval af at) (Interval bf bt) =
    let lw = case af of
            Nothing -> True
            Just af' -> case bf of
                Nothing  -> False
                Just bf' -> af' <= bf'
        hg = case at of
            Nothing -> True
            Just at' -> case bt of
                Nothing  -> False
                Just bt' -> at' >= bt'
    in
        lw && hg

-- | Check if an 'Interval' is empty.
isEmpty :: Ord a => Interval a -> Bool
isEmpty (Interval f t) = case f of
    Nothing -> False
    Just f' -> case t of
        Nothing -> False
        Just t' -> f' <= t'

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

-- | Check if a value is earlier than the beginning of an 'Interval'.
before :: Ord a => a -> Interval a -> Bool
before h (Interval f _) = case f of { Nothing -> False; Just h' -> h' > h; }

-- | Check if a value is later than the end of a 'Interval'.
after :: Ord a => a -> Interval a -> Bool
after h (Interval _ t) = case t of { Nothing -> False; Just t' -> h >= t'; }
