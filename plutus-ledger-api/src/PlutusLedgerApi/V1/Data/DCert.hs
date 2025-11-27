{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ViewPatterns #-}
{-# OPTIONS_GHC -Wno-simplifiable-class-constraints #-}
{-# OPTIONS_GHC -fno-omit-interface-pragmas #-}
{-# OPTIONS_GHC -fno-specialise #-}

-- | Digests of certificates that are included in transactions.
module PlutusLedgerApi.V1.Data.DCert
  ( DCert
  , pattern DCertDelegRegKey
  , pattern DCertDelegDeRegKey
  , pattern DCertDelegDelegate
  , pattern DCertPoolRegister
  , pattern DCertPoolRetire
  , pattern DCertGenesis
  , pattern DCertMir
  ) where

import Control.DeepSeq (NFData)
import GHC.Generics (Generic)
import PlutusLedgerApi.V1.Crypto (PubKeyHash)
import PlutusLedgerApi.V1.Data.Credential (StakingCredential)
import PlutusTx qualified
import PlutusTx.AsData qualified as PlutusTx
import PlutusTx.Blueprint.Definition (HasBlueprintDefinition (..))
import PlutusTx.Blueprint.Schema.Annotation (SchemaDescription (..), SchemaTitle (..))
import PlutusTx.Lift (makeLift)
import PlutusTx.Prelude qualified as P
import PlutusTx.Show (deriveShow)
import Prettyprinter.Extras (Pretty, PrettyShow (PrettyShow))

{-| A representation of the ledger DCert. Some information is digested, and
  not included -}
PlutusTx.asData
  [d|
    data DCert
      = DCertDelegRegKey StakingCredential
      | DCertDelegDeRegKey StakingCredential
      | DCertDelegDelegate
          StakingCredential
          -- \^ delegator
          PubKeyHash
      | -- \^ delegatee
        -- \| A digest of the PoolParams
        DCertPoolRegister
          PubKeyHash
          -- \^ poolId
          PubKeyHash
      | -- \^ pool VFR
        -- \| The retirement certificate and the Epoch in which the retirement will take place
        DCertPoolRetire PubKeyHash Integer -- NB: Should be Word64 but we only have Integer on-chain
      | -- \| A really terse Digest
        DCertGenesis
      | -- \| Another really terse Digest
        DCertMir
      deriving stock (Eq, Ord, Show, Generic)
      deriving newtype (PlutusTx.FromData, PlutusTx.UnsafeFromData, PlutusTx.ToData)
      deriving anyclass (NFData, HasBlueprintDefinition)
      deriving (Pretty) via (PrettyShow DCert)
    |]

{-# ANN DCertDelegRegKey (SchemaTitle "DCertDelegRegKey") #-}
{-# ANN DCertDelegRegKey (SchemaDescription "Delegation key registration certificate") #-}

{-# ANN DCertDelegDeRegKey (SchemaTitle "DCertDelegDeRegKey") #-}
{-# ANN DCertDelegDeRegKey (SchemaDescription "Delegation key deregistration certificate") #-}

{-# ANN DCertDelegDelegate (SchemaTitle "DCertDelegDelegate") #-}
{-# ANN DCertDelegDelegate (SchemaDescription "Delegation certificate") #-}

{-# ANN DCertPoolRegister (SchemaTitle "DCertPoolRegister") #-}
{-# ANN DCertPoolRegister (SchemaDescription "Pool registration certificate") #-}

{-# ANN DCertPoolRetire (SchemaTitle "DCertPoolRetire") #-}
{-# ANN DCertPoolRetire (SchemaDescription "Pool retirement certificate") #-}

{-# ANN DCertGenesis (SchemaTitle "DCertGenesis") #-}
{-# ANN DCertGenesis (SchemaDescription "Genesis key") #-}

{-# ANN DCertMir (SchemaTitle "DCertMir") #-}
{-# ANN DCertMir (SchemaDescription "MIR key") #-}

instance P.Eq DCert where
  {-# INLINEABLE (==) #-}
  DCertDelegRegKey sc == DCertDelegRegKey sc' = sc P.== sc'
  DCertDelegDeRegKey sc == DCertDelegDeRegKey sc' = sc P.== sc'
  DCertDelegDelegate sc pkh == DCertDelegDelegate sc' pkh' = sc P.== sc' && pkh P.== pkh'
  DCertPoolRegister pid pvfr == DCertPoolRegister pid' pvfr' = pid P.== pid' && pvfr P.== pvfr'
  DCertPoolRetire pkh i == DCertPoolRetire pkh' i' = pkh P.== pkh' && i P.== i'
  DCertGenesis == DCertGenesis = True
  DCertMir == DCertMir = True
  _ == _ = False

----------------------------------------------------------------------------------------------------
-- TH Splices --------------------------------------------------------------------------------------

makeLift ''DCert

deriveShow ''DCert
