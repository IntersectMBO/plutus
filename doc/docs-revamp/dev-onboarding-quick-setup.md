---
title: "Developer onboarding and quick setup guide"
description: "setting up and testing developer environment, writing first smart contract"
date: 2024-03-12
---

# Section 3. Developer onboarding and quick setup guide

This guide's objective is to help you set up your development environment, test it, and write your first smart contract within half a day. 

# Setting up and testing your development environment

## Prerequisites

### Hardware and OS requirements

**Processing power**
- Minimum: Intel Core i5 or AMD equivalent
- Recommended: Intel Core i7 or AMD Ryzen 7 

**RAM**
- Minimum: 8GB RAM
- Recommended: 16GB RAM or more

**Operating system**
- Linux: A recent distribution of Linux such as Ubuntu 20.04 LTS or later is preferred due to its widespread use in the Haskell community and its compatibility with Plutus tooling.
- macOS: macOS Catalina (10.15) or later
- Windows: While Windows can be used for Haskell development, it is less common and might require additional setup such as using Windows Subsystem for Linux (WSL2) to provide a Linux-compatible environment.

## Tools

To start developing with Haskell and Plutus, you'll need to set up your development environment with the essential tools. This section will guide you through installing and configuring the necessary components. 

### Nix

Nix is a package manager that provides reproducible and reliable software environments. It is particularly useful in Plutus development for managing dependencies and ensuring consistent development environments across different machines. 

While not strictly required, Nix is highly recommended because of its effective management of complex library dependencies. 

To install Nix, follow the instructions on the [official Nix website](https://nixos.org/download.html). 
After installing, configure Nix to use IOHK’s binary caches to speed up the build process. For important details and context, see these two documents: 
- [Contributing to Plutus > Installing and setting up Nix](https://github.com/IntersectMBO/plutus/blob/master/CONTRIBUTING.adoc),
- [Nix setup guide](https://github.com/input-output-hk/iogx/blob/main/doc/nix-setup-guide.md): instructions for installing and configuring Nix to work with projects at IOG.

### Haskell tool stack ("Stack")

Stack is a cross-platform program for developing Haskell projects. It handles dependency management, building, and testing your Haskell code. 

To install the Stack: 
1. Visit the [official Haskell Stack website](https://docs.haskellstack.org/). 
2. Follow the installation instructions for your operating system (Linux, macOS, or Windows).
3. Verify your installation by running `stack --version` in your terminal.

### GHC (Glasgow Haskell Compiler)

- GHC is the main compiler for Haskell with many extensions and optimizations. 
- To install GHC, run `stack setup`. Stack will automatically install the appropriate version of GHC for your project. 

### Cabal

Cabal is a system for building and packaging Haskell libraries and programs. It works well with Stack and is used to manage project dependencies and build configurations. Cabal is installed automatically when you install Stack. 

To verify your Cabal installation, run `cabal –version`. 

### Git

Make sure you have Git installed and configured. See [https://git-scm.com/](https://git-scm.com/). 

### IDE

An IDE provides a comprehensive environment for writing, testing, and debugging your Haskell code. Visual Studio Code (VS Code) is a widely used code editor that supports the Haskell extension. See [https://code.visualstudio.com/](https://code.visualstudio.com/). 

## Testing your environment setup

To verify that your environment is set up correctly and functioning, create and run a simple Haskell program. 

The following simple program fetches and displays the current system time and date. This example involves importing and using libraries to handle dates and times. 

### To create your test program

1. Create a new file named `Main.hs`. 
2. Add the following code to the file: 

```
import Data.Time
main :: IO ()
main = do
    currentTime <- getCurrentTime
    putStrLn $ "Current system time is: " ++ show currentTime
```

3. Open a terminal in VS Code. 
4. Navigate to the directory containing `Main.hs`. 
5. Run the command `stack runghc Main.hs`.
6. Verify that the output is correct. 

# Core concepts of Plutus smart contracts
Before we start building our first smart contract, let's go over the following core concepts that underpin Plutus smart contracts.

## Datum
A datum is a piece of data attached to a UTxO that represents the state required by the contract to validate transactions. For example, in a simple token transfer, the datum could include information such as the amount of tokens held in the UTxO or any conditions required for the transfer, such as a deadline for the transaction or the identity of the recipient. The datum is essential for the smart contract to enforce its logic and ensure that token transfers follow the rules specified by the contract.

## Redeemer
In the EUTxO model, a redeemer is a piece of data that accompanies a transaction input when attempting to spend a UTXO that is locked by a smart contract (also known as a script). The redeemer provides context or arguments that the smart contract needs to validate the transaction. It acts as a witness to satisfy the conditions imposed by the contract's validation script, enabling the contract to determine whether the transaction is permitted to consume the UTXO. 

## Script context
The script context is an object that provides information about the current state of the blockchain and the transaction being validated. It includes details such as the current time, the UTxOs being consumed and produced, and the signatories of the transaction. The script context is passed to the validator script, allowing it to make decisions based on the current state of the blockchain.

## Validator scripts
Validator scripts are Haskell functions that are the core components of Plutus smart contracts. They are responsible for validating transactions that interact with the contract's UTxOs. A validator script takes three inputs: the datum, the redeemer, and the script context. It uses this information to determine whether the transaction is valid according to the contract's logic. If the transaction is deemed valid, the validator script allows it to consume the contract's UTxOs and produce new ones.

# Writing your first Plutus smart contract

Now that you have a basic understanding of the core concepts, let's create a simple minimum lovelace validator contract. 

## Setting up a Plutus project
To set up a Plutus project for our minimum lovelace validator contract, follow these steps:

1. Create a new directory for your project and navigate to it in your terminal.

2. If you are using Nix, enter a Nix shell that provides the necessary development environment by running `nix develop` in your project directory. If you are not using Nix, make sure that all required C libraries are installed since PlutusTx depends on `cardano-base`, which in turn depends on cryptographic C libraries like `libblst`, `libsecp256k1`, and `libsodium`. 

3. Create a new directory named `src` and a new file named `MinLovelaceValidator.hs` inside it. This is where we'll write our smart contract code using Plutus Tx.

## Writing a simple minimum lovelace validator contract
With our project set up, let's walk through the process of writing a simple minimum lovelace validator contract step by step. This example illustrates one approach for implementing simple conditions within a Plutus smart contract. 

This smart contract example demonstrates a basic payment validation scenario where the smart contract enforces a minimum payment amount. A validator checks if a transaction meets a specific condition. The validator ensures that the total value spent in the transaction is at least 1000 lovelace. If the condition is not satisfied, the transaction is considered invalid.

The contract consists of the following conceptual stages:

1. Importing necessary modules and defining language extensions.
2. Defining the validator function (`mkValidator`) that checks the condition.
3. Creating a validator script using the compiled `mkValidator` function.
4. Defining a typed validator and its associated types.
5. Calculating the validator address based on the typed validator.

Here's a summary of the contract's functionality:

- The contract validates transactions based on a minimum lovelace requirement.
- It uses the `valueSpent` function to calculate the total value spent in the transaction.
- The `mkValidator` function checks if the spent value is at least 1000 lovelace.
- If the condition is not met, the transaction is invalidated.
- The contract defines a typed validator and its associated types using `BuiltinData`.
- The validator address is calculated based on the typed validator.

Now, let's go through the code step by step. 

### Step 1: Importing modules and defining language extensions

```haskell
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE NoImplicitPrelude   #-}
{-# LANGUAGE TemplateHaskell     #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeFamilies        #-}
{-# LANGUAGE TypeOperators       #-}
{-# LANGUAGE OverloadedStrings   #-}
import           Ledger                  (ValidatorCtx, TxOutTx, valueSpent)
import qualified Ledger.Typed.Scripts    as Scripts
import           Ledger.Ada              (lovelaceValueOf, fromValue)
import           PlutusTx                (compile)
import           PlutusTx.Prelude        hiding (Semigroup(..), unless)
import           Plutus.V1.Ledger.Scripts
import           Plutus.V1.Ledger.Api
```

This section includes the necessary language extensions and imports required for the contract. It brings in modules from the Plutus libraries, such as `Ledger`, `PlutusTx`, and `Plutus.V1.Ledger`.

### Step 2: Defining the validator function that checks the condition

```haskell
{-# INLINABLE mkValidator #-}
mkValidator :: BuiltinData -> BuiltinData -> BuiltinData -> ()
mkValidator _ _ ctx =
    let
        info = scriptContextTxInfo ctx
        val = valueSpent info
        hasEnoughLovelace = fromValue val >= 1000
    in
        unless hasEnoughLovelace $ error ()
```

The `mkValidator` function is the core of the contract. It takes three arguments of type `BuiltinData`, but only the third argument `ctx` is used. Inside the function:
- It extracts the transaction information from the validation context using `scriptContextTxInfo ctx`.
- It calculates the total value spent by the transaction using `valueSpent info`.
- It checks if the spent value contains at least 1000 lovelace using `fromValue val >= 1000`.
- If the condition is not met, it throws an error using `error ()`, which invalidates the transaction.

### Step 3: Creating a validator script using the compiled `mkValidator` function

```haskell
validator :: Validator
validator = mkValidatorScript $$(compile [|| mkValidator ||])
```

The `validator` value is defined as a `Validator` type. It is created using `mkValidatorScript` and the compiled version of the `mkValidator` function using Template Haskell.

### Step 4: Defining a typed validator and its associated types

```haskell
data Typed
instance Scripts.ValidatorTypes Typed where
    type instance DatumType Typed = BuiltinData
    type instance RedeemerType Typed = BuiltinData
```

The `Typed` data type is defined as a phantom type for the typed validator. An instance of `Scripts.ValidatorTypes` is defined for `Typed`, specifying that both the datum and redeemer types are `BuiltinData`.

```haskell
typedValidator :: Scripts.TypedValidator Typed
typedValidator = Scripts.mkTypedValidator @Typed
    $$(compile [|| mkValidator ||])
    $$(compile [|| wrap ||])
  where
    wrap = Scripts.wrapValidator @BuiltinData @BuiltinData
```

The `typedValidator` value is defined using `Scripts.mkTypedValidator`. It takes the compiled `mkValidator` function and a `wrap` function as arguments. The `wrap` function is defined using `Scripts.wrapValidator`, which wraps the `mkValidator` function to work with `BuiltinData` types.

### Step 5: Calculating the validator address based on the typed validator

```haskell
validatorAddress :: Ledger.Address
validatorAddress = Scripts.validatorAddress typedValidator
```

The `validatorAddress` value is defined using `Scripts.validatorAddress`. It takes the `typedValidator` as an argument and returns the corresponding validator address.

### Recap

The contract validates transactions based on a minimum lovelace requirement, using the `mkValidator` function. It defines a typed validator and its associated types using `BuiltinData`, and calculates the validator address based on the typed validator.

The use of `BuiltinData` as the datum and redeemer types allows for flexibility in the data that can be passed to the validator. The `wrap` function is used to convert between the `BuiltinData` types and the actual types expected by the `mkValidator` function.

## Testing and deploying your smart contract 

TODO
