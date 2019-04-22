{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE DerivingStrategies   #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE DeriveGeneric        #-}
{-# LANGUAGE TemplateHaskell      #-}
{-# LANGUAGE DeriveAnyClass       #-}
{-# LANGUAGE MonoLocalBinds       #-}
-- | A type for intervals and associated functions.
module Ledger.Interval(
      Interval(..)
    , interval
    , from
    , to
    , always
    ) where

import           Codec.Serialise.Class                    (Serialise)
import           Data.Aeson                               (FromJSON, ToJSON)
import           Data.Swagger.Internal.Schema             (ToSchema)
import           GHC.Generics                             (Generic)
import           Language.Haskell.TH

import           Language.PlutusTx.Lift                   (makeLift)

-- | An interval of @a@s. The interval is closed below and open above, meaning
--   that @Interval (Just (10 :: Int)) (Just 11)@ contains a single value @11@.
--   The interval is unbounded on either side: @Interval Nothing (Just 12)@
--   contains all numbers smaller than @12@.
data Interval a = Interval { ivFrom :: Maybe a, ivTo :: Maybe a }
    deriving (Eq, Ord, Show)
    deriving stock (Generic)
    deriving anyclass (ToSchema, FromJSON, ToJSON, Serialise)

makeLift ''Interval

{- note [Definition of Interval]

The purpose of this module is to provide an interval data type that
can be used in on-chain and off-chain code alike. Its two main uses in the
'wallet-api' module are the validity range of transactions, and the ranges of
funds and slot numbers for wallet triggers.

To ensure that 'Interval' can be used in on-chain code, the functions in this
module do not use type classes or functions from the Haskell Prelude. There are
query functions specialized to 'Interval Slot' exported from 'Ledger.Slot'.
-}

-- | An 'Interval' that covers every slot.
always :: Q (TExp (Interval a))
always = [|| Interval Nothing Nothing ||]

-- | @from a@ is an 'Interval' that includes all values that are
--  greater than or equal to @a@.
from :: Q (TExp (a -> Interval a))
from = [|| \s -> Interval (Just s) Nothing ||]

-- | @to a@ is an 'Interval' that includes all values that are
--  smaller than @a@.
to :: Q (TExp (a -> Interval a))
to = [|| \s -> Interval Nothing (Just s) ||]

-- | @interval a b@ includes all values that are greater than or equal
--   to @a@ and smaller than @b@. Therefore it includes @a@ but not it
--   does not include @b@.
interval :: Q (TExp (a -> a -> Interval a))
interval = [|| \s s' -> Interval (Just s) (Just s') ||]
