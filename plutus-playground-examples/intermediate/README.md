# Exemples Plutus — Niveau Intermédiaire

Ce dossier contient **3 exemples Plutus intermédiaires**, destinés aux développeurs ayant déjà compris les bases (validators simples, logique élémentaire, signatures) et souhaitant progresser.

Chaque exemple peut être testé avec :

* **Plutus Playground (classique)**
* **Plutus Playground Demeter (version moderne recommandée)**
* **Compilation locale (via Cabal)**

---

# Comment exécuter les exemples

## 1. Via Plutus Playground Demeter (recommandé)

Demeter est une plateforme moderne qui permet :

* de compiler les scripts Plutus v1 et v2
* d’utiliser des templates prêts à l’emploi
* de simuler facilement les transactions

Accès :
[https://demeter.run/playground](https://demeter.run/playground)

### Étapes pour tester un script :

1. Ouvrir la Playground Demeter
2. Choisir un modèle "Custom Contract"
3. Coller le code de l'exemple
4. Compiler
5. Injecter le datum et le redeemer
6. Simuler une transaction

---

## 2. Via le Plutus Playground (ancien)

Accès : [https://playground.plutus.iohkdev.io/](https://playground.plutus.iohkdev.io/)

Procédure :

1. Créer un nouveau script
2. Coller le code
3. Compiler
4. Simuler la transaction

---

## 3. Compilation locale

### Prérequis

* GHC 8.10.7
* cabal 3.6+
* plutus-apps / dépendances Plutus installées

### Commandes

```
cabal update
cabal build
```

---

# Contenu du dossier

Les scripts intermédiaires inclus :

* **Lottery.hs** — Gestion d'un tirage au sort
* **MultiSig.hs** — Validator nécessitant deux signatures
* **VotingContract.hs** — Contrat de vote simple

---

# Exemple 1 : Lottery (Tirage au sort)

## Description

Ce smart contract permet :

* d'enregistrer une liste de participants
* de fixer un gagnant à l'aide d’un `Maybe PubKeyHash`
* de valider uniquement si un gagnant est défini

## Objectif pédagogique

* Manipulation de structures de données complexes
* Utilisation de `Maybe`
* Construction de `Datum` personnalisés

## Exemple de Datum (Playground ou Demeter)

```
{
  "participants": ["pubKeyHash1", "pubKeyHash2"],
  "winner": null
}
```

---

## Code : Lottery.hs

```haskell
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE NoImplicitPrelude   #-}
{-# LANGUAGE TemplateHaskell     #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE OverloadedStrings   #-}
module Lottery where

import           PlutusTx
import           PlutusTx.Prelude
import           Ledger
import           Ledger.Typed.Scripts
import           Ledger.Value

data LotteryDatum = LotteryDatum
    { participants :: [PubKeyHash]
    , winner :: Maybe PubKeyHash
    } deriving Show

PlutusTx.unstableMakeIsData ''LotteryDatum

data Lottery
instance Scripts.ValidatorTypes Lottery where
    type instance DatumType Lottery = LotteryDatum
    type instance RedeemerType Lottery = ()

lotteryValidator :: LotteryDatum -> () -> ScriptContext -> Bool
lotteryValidator datum _ ctx =
    case winner datum of
        Nothing -> traceIfFalse "No winner yet" False
        Just p  -> True

typedLotteryValidator :: Scripts.TypedValidator Lottery
typedLotteryValidator = Scripts.mkTypedValidator @Lottery
    $$(PlutusTx.compile [|| lotteryValidator ||])
    $$(PlutusTx.compile [|| wrap ||])
  where
    wrap = Scripts.wrapValidator @LotteryDatum @()
```

---

# Exemple 2 : Multi-Signature Validator

## Objectif pédagogique

Apprendre à :

* récupérer les signatures dans `txInfoSignatories`
* appliquer une logique multi-signatures
* renvoyer des erreurs claires via `traceIfFalse`

---

## Code : MultiSig.hs

```haskell
{-# LANGUAGE DataKinds        #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE ScopedTypeVariables #-}

module MultiSig where

import           PlutusTx
import           PlutusTx.Prelude
import           Ledger
import           Ledger.Contexts
import           Ledger.Typed.Scripts
import           Prelude (Semigroup(..))

data MultiSigParams = MultiSigParams
  { signerA :: PubKeyHash
  , signerB :: PubKeyHash
  }
PlutusTx.unstableMakeIsData ''MultiSigParams

{-# INLINABLE mkValidator #-}
mkValidator :: MultiSigParams -> () -> ScriptContext -> Bool
mkValidator params _ ctx =
    traceIfFalse "Missing signatures" signaturesOk
  where
    info = scriptContextTxInfo ctx
    sigs = txInfoSignatories info
    signaturesOk =
         signerA params `elem` sigs
      && signerB params `elem` sigs

data MS
instance ValidatorTypes MS where
    type instance DatumType MS = MultiSigParams
    type instance RedeemerType MS = ()

typedValidator :: TypedValidator MS
typedValidator = mkTypedValidator @MS
    $$(PlutusTx.compile [|| mkValidator ||])
    $$(PlutusTx.compile [|| wrap ||])
  where
    wrap = wrapValidator @MultiSigParams @()

validator :: Validator
validator = validatorScript typedValidator
```

---

## Test dans Playground / Demeter

* Signer avec un seul wallet → rejet
* Signer avec deux wallets (signerA et signerB) → accepté

---

# Exemple 3 : Voting Contract

## Description

Smart contract pour un vote simple :

* `candidates` : liste des candidats
* `votes` : liste de paires `(candidat, nbVotes)`
* Un vote n'est accepté que si le candidat existe

## Exemple de Datum pour tests

```
{
  "candidates": ["Alice", "Bob"],
  "votes": [["Alice", 0], ["Bob", 0]]
}
```

---

## Code : VotingContract.hs

```haskell
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE NoImplicitPrelude   #-}
{-# LANGUAGE TemplateHaskell     #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE OverloadedStrings   #-}
module VotingContract where

import PlutusTx
import PlutusTx.Prelude
import Ledger
import Ledger.Typed.Scripts

data VoteDatum = VoteDatum
    { candidates :: [BuiltinByteString]
    , votes :: [(BuiltinByteString, Integer)]
    } deriving Show

PlutusTx.unstableMakeIsData ''VoteDatum

data Voting
instance Scripts.ValidatorTypes Voting where
    type instance DatumType Voting = VoteDatum
    type instance RedeemerType Voting = BuiltinByteString

votingValidator :: VoteDatum -> BuiltinByteString -> ScriptContext -> Bool
votingValidator datum candidate _ =
    candidate `elem` candidates datum

typedVotingValidator :: Scripts.TypedValidator Voting
typedVotingValidator = Scripts.mkTypedValidator @Voting
    $$(PlutusTx.compile [|| votingValidator ||])
    $$(PlutusTx.compile [|| wrap ||])
  where
    wrap = Scripts.wrapValidator @VoteDatum @BuiltinByteString
```

---

# Objectif pédagogique global

Les trois contrats permettent d’apprendre :

* structures de données complexes (`Maybe`, tuples, listes)
* gestion des signatures
* manipulation des Datum / Redeemer
* validation logique
* lecture du `ScriptCo
