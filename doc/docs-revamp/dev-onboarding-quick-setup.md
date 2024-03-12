---
title: "Developer onboarding and quick setup guide"
description: "setting up and testing developer environment, writing first smart contract"
date: 2024-03-12
---

This guide's objective is to help you set up your development environment, test it, and write your first smart contract within half a day. 

# 3. Setting up and testing your development environment

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

# Core Concepts of Plutus Smart Contracts
Before we start building our first smart contract, let's go over the following core concepts that underpin Plutus smart contracts.

## Datum
A datum is a piece of data attached to a UTxO that represents the state required by the contract to validate transactions. For example, in a simple token transfer, the datum could include information such as the amount of tokens held in the UTxO or any conditions required for the transfer, such as a deadline for the transaction or the identity of the recipient. The datum is essential for the smart contract to enforce its logic and ensure that token transfers follow the rules specified by the contract.

## Redeemer
In the EUTxO model, a redeemer is a piece of data that accompanies a transaction input when attempting to spend a UTXO that is locked by a smart contract (also known as a script). The redeemer provides context or arguments that the smart contract needs to validate the transaction. It acts as a witness to satisfy the conditions imposed by the contract's validation script, enabling the contract to determine whether the transaction is permitted to consume the UTXO. 

## Script Context
The script context is an object that provides information about the current state of the blockchain and the transaction being validated. It includes details such as the current time, the UTxOs being consumed and produced, and the signatories of the transaction. The script context is passed to the validator script, allowing it to make decisions based on the current state of the blockchain.

## Validator Scripts
Validator scripts are Haskell functions that are the core components of Plutus smart contracts. They are responsible for validating transactions that interact with the contract's UTxOs. A validator script takes three inputs: the datum, the redeemer, and the script context. It uses this information to determine whether the transaction is valid according to the contract's logic. If the transaction is deemed valid, the validator script allows it to consume the contract's UTxOs and produce new ones.

# Writing your first Plutus smart contract: A simple token transfer

**NOTE: The following is a placeholder example contract. TBD.** 

Now that you have a basic understanding of the core concepts, let's create a simple token transfer contract. 

## Setting Up a Plutus Project
To set up a Plutus project for our token transfer contract, follow these steps:

1. Create a new directory for your project and navigate to it in your terminal.

2. If you are using Nix, enter a Nix shell that provides the necessary development environment by running `nix develop` in your project directory. If you are not using Nix, make sure that all required C libraries are installed since PlutusTx depends on `cardano-base`, which in turn depends on cryptographic C libraries like `libblst`, `libsecp256k1`, and `libsodium`. 

3. Create a new directory named `src` and a new file named `TokenTransfer.hs` inside it. This is where we'll write our smart contract code using the Plutus Tx.

## Writing a Simple Token Transfer Contract
With our project set up, let's walk through the process of writing a simple token transfer contract step by step.

### Step 1: Define the Token Data Type
First, we need to define a data type that represents the token we want to transfer. Open the `TokenTransfer.hs` file and add the following code:

```haskell
data Token = Token
    { tokenName   :: TokenName
    , tokenAmount :: Integer
    } deriving Show

PlutusTx.unstableMakeIsData ''Token
```

This code defines a `Token` data type with two fields: `tokenName` and `tokenAmount`. The `PlutusTx.unstableMakeIsData` function is used to make the data type serializable, which is required for storing it on the blockchain.

### Step 2: Define the Redeemer Data Type 
Next, we need to define a data type for the redeemer, which will contain the information needed to perform the token transfer:

```haskell
data TransferRedeemer = TransferToken
    { recipient :: PaymentPubKeyHash
    , amount    :: Integer
    } deriving Show

PlutusTx.unstableMakeIsData ''TransferRedeemer
```

The `TransferRedeemer` data type has two fields: `recipient`, which is the public key hash of the recipient's address, and `amount`, which is the number of tokens to be transferred.

### Step 3: Write the Validator Script 
The validator script is the heart of our smart contract. It defines the conditions under which a token transfer is considered valid:

```haskell
{-# INLINABLE mkValidator #-}
mkValidator :: Token -> TransferRedeemer -> ScriptContext -> Bool
mkValidator token redeemer _ =
    let token' = Token (tokenName token) (amount redeemer)
    in traceIfFalse "Insufficient funds" (tokenAmount token >= amount redeemer) &&
       traceIfFalse "Invalid amount" (amount redeemer > 0)
```

This validator script checks two conditions:
1. The token balance in the UTxO is greater than or equal to the requested transfer amount.
2. The requested transfer amount is greater than zero.

If both conditions are met, the token transfer is considered valid.

### Step 4: Compile the Validator Script 
To use the validator script in our smart contract, we need to compile it:

```haskell
validator :: Scripts.Validator
validator = Scripts.mkValidatorScript $$(PlutusTx.compile [|| mkValidator ||])
```

This code compiles the `mkValidator` function into a Plutus Core script and wraps it in a `Validator` object.

### Step 5: Define the Token Transfer Function 
Finally, we need to define a function that performs the actual token transfer:

```haskell
transfer :: Token -> TransferRedeemer -> Contract w s Text ()
transfer token redeemer = do
    let val = Value.singleton (tokenName token) (tokenAmount token)
        r   = Redeemer $ PlutusTx.toData redeemer
        tx  = Constraints.mustPayToTheScript token val <> 
              Constraints.mustSpendScriptOutput (scriptAddress validator) r
    ledgerTx <- submitTxConstraints validator tx
    void $ awaitTxConfirmed $ txId ledgerTx
    logInfo @String $ "Transferred " ++ show (amount redeemer) ++ " tokens to " ++ show (recipient redeemer)
```

This function takes the `Token` and `TransferRedeemer` as input and constructs a transaction that transfers the specified amount of tokens to the recipient's address. The transaction is then submitted to the blockchain, and a confirmation message is logged.

## Testing and Deploying Your Smart Contract 

TODO
