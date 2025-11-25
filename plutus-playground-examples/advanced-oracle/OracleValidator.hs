{-# LANGUAGE DataKinds #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE OverloadedStrings #-}

module OracleValidator where

import Plutus.V2.Ledger.Api
import PlutusTx
import PlutusTx.Prelude hiding (Semigroup(..))
import Prelude (Semigroup(..))

import Types (OracleDatum(..))

{-# INLINABLE mkOracleValidator #-}
mkOracleValidator :: TokenName -> PubKeyHash -> OracleDatum -> OracleDatum -> ScriptContext -> Bool
mkOracleValidator tn updaterPkh oldDatum newDatum ctx =
    traceIfFalse "NFT manquant" nftPresent  &&
    traceIfFalse "signature invalide" signedByUpdater &&
    traceIfFalse "variation trop élevée" priceChangeOK
  where
    info :: TxInfo
    info = scriptContextTxInfo ctx

    -- Vérifier présence du NFT identitaire
    nftPresent :: Bool
    nftPresent =
        let
            v = valuePaidTo info (ownHash ctx)
        in valueOf v (ownCurrencySymbol ctx) tn == 1

    -- Vérifier signature du validateur Oracle off-chain updater
    signedByUpdater :: Bool
    signedByUpdater = txSignedBy info updaterPkh

    priceChangeOK :: Bool
    priceChangeOK =
        let old = odPrice oldDatum
            new = odPrice newDatum
        in abs (new - old) <= 5 -- 5% max

{-# INLINABLE wrapped #-}
wrapped :: TokenName -> PubKeyHash -> BuiltinData -> BuiltinData -> BuiltinData -> ()
wrapped tn pkh d r c =
    check ( mkOracleValidator tn pkh
        (PlutusTx.unsafeFromBuiltinData d)
        (PlutusTx.unsafeFromBuiltinData r)
        (PlutusTx.unsafeFromBuiltinData c)
    )

validator :: TokenName -> PubKeyHash -> Validator
validator tn pkh = mkValidatorScript $
    $$(PlutusTx.compile [|| wrapped ||])
        `PlutusTx.applyCode` PlutusTx.liftCode tn
        `PlutusTx.applyCode` PlutusTx.liftCode pkh
