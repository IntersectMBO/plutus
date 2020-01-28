{-# LANGUAGE DeriveAnyClass             #-}
{-# LANGUAGE DeriveGeneric              #-}
{-# LANGUAGE DerivingStrategies         #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE OverloadedStrings          #-}
{-# LANGUAGE RecordWildCards            #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE TypeApplications           #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

-- | Temporary scaffolding - this is something easy and ledger-like
-- that I can use while we're waiting for real events.
--
-- In this simulation we can easily create transactions that move
-- money between different users by posting equal and opposite
-- entries to their accounts.
--
-- This gives us some dummy data we can easily ask some interesting
-- questions of, like, "Do the account balance?", and "Who owns what
-- now?"
module Plutus.SCB.Events.Mock where

import           Data.Aeson          (FromJSON, ToJSON)
import qualified Data.Set            as Set
import           Data.Text           (Text)
import           GHC.Generics        (Generic)
import           Ledger.Ada          (lovelaceValueOf)
import           Ledger.Value        (Value, scale)
import           Plutus.SCB.Relation (Table)
import qualified Plutus.SCB.Relation as Relation
import           Test.QuickCheck     (Arbitrary, arbitrary, elements)

newtype AccountId =
    AccountId
        { unAccountId :: Int
        }
    deriving (Show, Eq, Generic, Ord)
    deriving newtype (Num, FromJSON, ToJSON)

instance Arbitrary AccountId where
    arbitrary =
        elements $ maybe [] Set.toList $ Relation.extract $ Relation.keys users

users :: Table AccountId Text
users =
    Relation.fromList
        [(0, "Bank"), (1, "Jann"), (2, "Michael"), (3, "David"), (4, "Kris")]

data Entry =
    Entry
        { accountId :: AccountId
        , amount    :: Value
        }
    deriving (Show, Eq, Generic, FromJSON, ToJSON)

instance Arbitrary Value where
    arbitrary = elements (lovelaceValueOf <$> [1 .. 100])

instance Arbitrary Entry where
    arbitrary = do
        accountId <- arbitrary
        amount <- arbitrary
        pure Entry {..}

newtype Tx =
    Tx
        { entries :: [Entry]
        }
    deriving (Show, Eq)

instance Arbitrary Tx where
    arbitrary = do
        from :: AccountId <- arbitrary
        to <- arbitrary
        value <- arbitrary
        pure
            Tx
                { entries =
                      [ Entry {accountId = from, amount = value}
                      , Entry
                            { accountId = to
                            , amount = scale @Integer @Value (-1) value
                            }
                      ]
                }
