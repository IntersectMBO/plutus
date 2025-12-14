{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ViewPatterns #-}

module PlutusBenchmark.Coop.Types where

import Prelude qualified as HS

import Control.Lens (makeFields)
import PlutusLedgerApi.V1.Value (AssetClass)
import PlutusLedgerApi.V3
  ( Address
  , CurrencySymbol
  , Extended
  , LedgerBytes
  , POSIXTime
  , POSIXTimeRange
  , PubKeyHash
  )
import PlutusTx.IsData qualified as PlutusTx
import PlutusTx.Lift qualified as PlutusTx
import PlutusTx.Prelude

-- | A fact statement is just Plutus Data
type FactStatement = BuiltinData

-- | A fact statement ID is just bytes
type FactStatementId = LedgerBytes

-- | A datum holding the FactStatement that's locked at @FsV
data FsDatum = FsDatum
  { fd'fs :: FactStatement
  -- ^ Fact statement
  , fd'fsId :: FactStatementId
  -- ^ Fact statement ID as provided by the oracle
  , fs'gcAfter :: Extended POSIXTime
  -- ^ After this time the Submitter can 'garbage collect' the @FsV UTxO
  , fs'submitter :: PubKeyHash
  -- ^ Public key hash of the wallet that submitted the $FS minting transaction
  }
  deriving stock (HS.Show, HS.Eq)

-- | FsMp initial parameters
data FsMpParams = FsMpParams
  { fmp'coopAc :: AssetClass
  -- ^ \$COOP one-shot token asset class denoting the COOP instance
  , fmp'fsVAddress :: Address
  -- ^ @FsV fact statement validator address where the minted $FS tokens are paid to
  , fmp'authParams :: AuthParams
  -- ^ Authentication parameters
  }
  deriving stock (HS.Show, HS.Eq)

-- | FsMp initial authentication parameters
data AuthParams = AuthParams
  { ap'authTokenCs :: CurrencySymbol
  -- ^ \$AUTH token CurrencySymbol required to authorize $FS minting
  , ap'certTokenCs :: CurrencySymbol
  -- ^ \$CERT token CurrencySymbol required to authorize $FS minting
  }
  deriving stock (HS.Show, HS.Eq)

-- | FsMp redeemer denoting $FS mint or burning actions
data FsMpRedeemer = FsMpBurn | FsMpMint
  deriving stock (HS.Show, HS.Eq)

-- ** COOP Authentication

-- | Authentication batch identifier (certificates + authentication tokens)
type AuthBatchId = LedgerBytes

-- | Datum locked at @CertV containing information about $AUTH tokens used in authorizing $FS minting
data CertDatum = CertDatum
  { cert'id :: AuthBatchId
  -- ^ Certificate unique identifier (matches $CERT and $AUTH token names)
  , cert'validity :: POSIXTimeRange
  -- ^ Certificate validity interval after which associated $AUTH tokens can't be used to authorize $FS minting
  , cert'redeemerAc :: AssetClass
  -- ^ \$CERT-RMDR asset class that must be spent to 'garbage collect' the @CertV UTxO after the certificate had expired
  }
  deriving stock (HS.Show, HS.Eq)

-- | CertMp redeemer denoting $CERT mint or burning actions
data CertMpRedeemer = CertMpBurn | CertMpMint
  deriving stock (HS.Show, HS.Eq)

-- | CertMp initial parameters
data CertMpParams = CertMpParams
  { cmp'authAuthorityAc :: AssetClass
  -- ^ \$AA (Authentication authority) tokens required to authorize $CERT minting
  , cmp'requiredAtLeastAaQ :: Integer
  -- ^ \$AA token quantity required to authorize $CERT minting
  , cmp'certVAddress :: Address
  -- ^ Certificate validator @CertV address to pay the $CERT tokens to
  }
  deriving stock (HS.Show, HS.Eq)

-- | AuthMp redeemer denoting $AUTH mint or burning actions
data AuthMpRedeemer = AuthMpBurn | AuthMpMint
  deriving stock (HS.Show, HS.Eq)

-- | AuthMp initial parameters
data AuthMpParams = AuthMpParams
  { amp'authAuthorityAc :: AssetClass
  -- ^ \$AA (Authentication authority) tokens required to authorize $AUTH minting
  , amp'requiredAtLeastAaQ :: Integer
  -- ^ \$AA token quantity required to authorize $AUTH minting
  }
  deriving stock (HS.Show, HS.Eq)

PlutusTx.unstableMakeIsData ''AuthParams

PlutusTx.unstableMakeIsData ''FsDatum
PlutusTx.unstableMakeIsData ''CertDatum

PlutusTx.unstableMakeIsData ''FsMpParams
PlutusTx.unstableMakeIsData ''FsMpRedeemer
PlutusTx.unstableMakeIsData ''CertMpParams
PlutusTx.unstableMakeIsData ''CertMpRedeemer
PlutusTx.unstableMakeIsData ''AuthMpParams
PlutusTx.unstableMakeIsData ''AuthMpRedeemer

PlutusTx.makeLift ''AuthParams
PlutusTx.makeLift ''FsMpParams
PlutusTx.makeLift ''CertMpParams
PlutusTx.makeLift ''AuthMpParams

-- | Lenses
makeFields ''FsDatum
makeFields ''CertDatum

makeFields ''FsMpParams
makeFields ''FsMpRedeemer
makeFields ''CertMpParams
makeFields ''CertMpRedeemer
makeFields ''AuthMpParams
makeFields ''AuthMpRedeemer
makeFields ''AuthParams
