# Oracle NFT Stateful — Exemple Avancé (Plutus)

Cet exemple montre comment construire un **Oracle stateful** basé sur UTXO, sécurisé par un **NFT d'identité**, avec logique de mise à jour on-chain.

Ce pattern est essentiel pour:

* les DEX (prix ADA/USD),
* les protocoles de lending,
* les protocoles de dérivés,
* les real-world feeds off-chain → on-chain.

---

# Objectif

Créer un **Oracle UTXO unique**, protégé par un NFT, et permettant :

1. d'émettre un oracle initial (UTxO + NFT),
2. d’autoriser une mise à jour du prix uniquement si :

   * le NFT reste dans le même script,
   * un signataire spécifique signe la transaction,
   * la nouvelle valeur respecte un "change limit".

---

# Fichiers

* `OracleValidator.hs` : Validator complet du script
* `Types.hs` : Types du payload Oracle

---

# Test dans Plutus Playground

1. Copier les fichiers dans la section Haskell du Playground.
2. Compiler.
3. Créer un **UTxO initial** contenant :

   * `oracleNFT`,
   * `Datum` = prix initial.
4. Faire une transaction de mise à jour avec un nouveau prix.
5. Vérifier que :

   * Sans NFT → rejet
   * Sans signature → rejet
   * Variation > limite → rejet
   * Variation raisonnable → accepté

---

# Code — OracleValidator.hs

```haskell
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

    nftPresent :: Bool
    nftPresent =
        let
            v = valuePaidTo info (ownHash ctx)
        in valueOf v (ownCurrencySymbol ctx) tn == 1

    signedByUpdater :: Bool
    signedByUpdater = txSignedBy info updaterPkh

    priceChangeOK :: Bool
    priceChangeOK =
        let old = odPrice oldDatum
            new = odPrice newDatum
        in abs (new - old) <= 5

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
```
