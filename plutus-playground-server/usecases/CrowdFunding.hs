{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE DeriveGeneric       #-}
{-# LANGUAGE DeriveAnyClass      #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE RecordWildCards     #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell     #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE NoImplicitPrelude   #-}
{-# OPTIONS_GHC -fno-ignore-interface-pragmas #-}
module CrowdFunding where
-- TRIM TO HERE
-- Crowdfunding contract implemented using the [[Plutus]] interface.
-- This is the fully parallel version that collects all contributions
-- in a single transaction.
--
-- Note [Transactions in the crowdfunding campaign] explains the structure of
-- this contract on the blockchain.

import qualified Language.PlutusTx            as PlutusTx
import           Language.PlutusTx.Prelude
import           Ledger.Slot                  (SlotRange)
import qualified Ledger.Slot                  as Slot
import           Ledger
import           Ledger.Validation            as V
import           Ledger.Value                 (Value)
import qualified Ledger.Value                 as VTH
import           Playground.Contract
import           Wallet                       as W
import qualified Wallet.Emulator              as EM
import           Wallet.Emulator             (Wallet)
import Data.Proxy
import Schema (toSchema,SimpleArgumentSchema)
-- | A crowdfunding campaign.
data Campaign = Campaign
    { campaignDeadline           :: Slot
    -- ^ The date by which the campaign target has to be met
    , campaignTarget             :: Value
    -- ^ Target amount of funds
    , campaignCollectionDeadline :: Slot
    -- ^ The date by which the campaign owner has to collect the funds
    , campaignOwner              :: PubKey
    -- ^ Public key of the campaign owner. This key is entitled to retrieve the
    --   funds if the campaign is successful.
    } deriving (Generic, ToJSON, FromJSON, ToSchema)
