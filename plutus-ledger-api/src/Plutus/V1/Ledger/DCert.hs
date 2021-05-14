{-# LANGUAGE DataKinds         #-}
{-# LANGUAGE DeriveAnyClass    #-}
{-# LANGUAGE DerivingVia       #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell   #-}
{-# OPTIONS_GHC -fno-specialise #-}
{-# OPTIONS_GHC -fno-strictness #-}
{-# OPTIONS_GHC -Wno-simplifiable-class-constraints #-}
{-# OPTIONS_GHC -fno-omit-interface-pragmas #-}

{-

Digests of certificates that are included in transactions.

-}
module Plutus.V1.Ledger.DCert(DCert(..)) where

import           Codec.Serialise.Class       (Serialise)
import           Control.DeepSeq             (NFData)
import           Data.Aeson                  (FromJSON, ToJSON)
import           Data.Hashable               (Hashable)
import           Data.Text.Prettyprint.Doc   (Pretty (..), viaShow)
import           GHC.Generics                (Generic)
import           Plutus.V1.Ledger.Credential (StakingCredential)
import           Plutus.V1.Ledger.Crypto     (PubKeyHash)
import qualified PlutusTx                    as PlutusTx

-- | A representation of the ledger DCert. Some information is digested, and
--   not included
data DCert
  = DCertDelegRegKey StakingCredential
  | DCertDelegDeRegKey StakingCredential
  | DCertDelegDelegate
      StakingCredential
      -- ^ delegator
      PubKeyHash
      -- ^ delegatee
  | -- | A digest of the PoolParams
    DCertPoolRegister
      PubKeyHash
      -- ^ poolId
      PubKeyHash
      -- ^ pool VFR
  | -- | The retiremant certificate and the Epoch N
    DCertPoolRetire PubKeyHash Integer -- NB: Should be Word64 but we only have Integer on-chain
  | -- | A really terse Digest
    DCertGenesis
  | -- | Another really terse Digest
    DCertMir
    deriving stock (Eq, Ord, Show, Generic)
    deriving anyclass (ToJSON, FromJSON, Serialise, Hashable, NFData)

instance Pretty DCert where
  pretty = viaShow

PlutusTx.makeIsDataIndexed
    ''DCert
    [ ('DCertDelegRegKey,0)
    , ('DCertDelegDeRegKey,1)
    , ('DCertDelegDelegate,2)
    , ('DCertPoolRegister,3)
    , ('DCertPoolRetire,4)
    , ('DCertGenesis,5)
    , ('DCertMir,6)
    ]
PlutusTx.makeLift ''DCert
