# Exemples Plutus — Niveau Débutants

Ce dossier contient **3 exemples très simples et entièrement expliqués** pour aider les nouveaux développeurs à apprendre Plutus en moins de **15 minutes**.

L’objectif est d’avoir des scripts :

* faciles à comprendre
* faciles à modifier
* faciles à exécuter dans **Demeter / Plutus Tx**
* utiles pour apprendre la logique des validators

Ces exemples couvrent les bases :

1. Un contrat Hello World (validator trivial)
2. Un script de verrouillage/déverrouillage (Always True + Datum)
3. Un script de donation simple (valide si l’utilisateur signe la transaction)

---

# 1. Exemple : Hello World (AlwaysSucceeds)

## Objectif

Créer le plus petit script Plutus possible : il accepte **toutes les transactions**.

## Code (`example1_hello_world.hs`)

```haskell
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE TemplateHaskell #-}

module HelloWorld where

import PlutusTx
import PlutusTx.Prelude
import Ledger
import Ledger.Typed.Scripts

-- Validator trivial : toujours vrai
{-# INLINABLE mkValidator #-}
mkValidator :: BuiltinData -> BuiltinData -> BuiltinData -> ()
mkValidator _ _ _ = ()

validator :: Validator
validator = mkValidatorScript $$(PlutusTx.compile [|| mkValidator ||])
```

## Exécution avec Demeter / Plutus Tx localement

1. Copier le fichier `example1_hello_world.hs` dans `src/`.
2. Dans le terminal du workspace Demeter :

```bash
cabal update
cabal build
```

3. Le script sera compilé et prêt à être simulé dans Demeter.

---

# 2. Exemple : Script de verrouillage / déverrouillage

## Objectif

Un script où :

* on peut verrouiller des fonds
* on peut les débloquer seulement si un **mot de passe (datum)** correspond

## Code (`example2_lock_unlock.hs`)

```haskell
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE TemplateHaskell #-}

module LockUnlock where

import PlutusTx
import PlutusTx.Prelude
import Ledger
import Ledger.Typed.Scripts

{-# INLINABLE mkValidator #-}
mkValidator :: BuiltinByteString -> BuiltinByteString -> BuiltinData -> ()
mkValidator expected actual _ =
    if expected == actual
        then ()
        else error ()

validator :: Validator
validator =
    mkValidatorScript $$(PlutusTx.compile [|| mkValidator ||])
```

## Simulation avec Demeter

1. Définir un **datum**, ex: `"1234"`.
2. Définir un **redeemer**, ex: `"1234"`.
3. Si datum = redeemer → transaction validée.
4. Sinon → transaction échoue.

---

# 3. Exemple : Script de donation simple (signature requise)

## Objectif

Contrat qui n’autorise la dépense que si une adresse **signée** est dans la transaction.

## Code (`example3_donation_validator.hs`)

```haskell
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE TemplateHaskell #-}

module DonationValidator where

import PlutusTx
import PlutusTx.Prelude
import Ledger
import Ledger.Typed.Scripts

{-# INLINABLE mkValidator #-}
mkValidator :: PubKeyHash -> BuiltinData -> BuiltinData -> ScriptContext -> ()
mkValidator pkh _ _ ctx =
    if txSignedBy (scriptContextTxInfo ctx) pkh
        then ()
        else error ()

validator :: PubKeyHash -> Validator
validator pkh = mkValidatorScript $$(PlutusTx.compile [|| mkValidator ||])
```

## Simulation avec Demeter

1. Mettre ton **PubKeyHash** dans le script.
2. Dépenser les fonds depuis le script.
3. Si le wallet correspondant signe → transaction réussie.
4. Sinon → transaction échoue.

---

# Installation locale avec Demeter

1. Installer [Demeter / Plutus Tx](https://github.com/input-output-hk/plutus-apps) sur votre machine.
2. Copier vos fichiers `.hs` dans `src/`.
3. Dans le workspace du projet :

```bash
cabal update
cabal build
```

> ⚠️ Plutus et ses packages (`plutus-tx`, `ledger`) ne sont pas sur Hackage. Il faut utiliser le workspace Demeter / Nix pour compiler.

---

# Structure du dossier

```
simple/
 ├── example1_hello_world.hs
 ├── example2_lock_unlock.hs
 ├── example3_donation_validator.hs
 └── README.md
```

---

# Contribution

Ces exemples sont conçus pour des débutants absolus.
N’hésitez pas à proposer :

* des variantes
* des améliorations pédagogiques
* de nouvelles explications

Merci de contribuer à l’écosystème Cardano !
