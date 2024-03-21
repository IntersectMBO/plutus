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

```haskell
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
Before we start building our vesting smart contract, let's go over the following core concepts that underpin Plutus smart contracts.

## Datum
In a vesting contract, the datum represents the state and conditions of the vesting agreement. It includes information such as the beneficiary's public key hash and the deadline for the vesting period. The datum is attached to the UTxO that holds the vested funds and is used by the contract's validator script to enforce the vesting conditions. It ensures that the funds can only be released to the beneficiary after the specified deadline has passed.

## Redeemer
In the context of a vesting contract, the redeemer is typically not used, as the contract's logic does not require any additional input from the transaction. The validation of the transaction is based solely on the datum (vesting conditions) and the script context, such as checking if the deadline has passed and if the transaction is signed by the beneficiary. However, if required, a redeemer could be used to provide additional arguments to the validator script.

## Script context
The script context is crucial for a vesting contract as it provides information about the current state of the blockchain and the transaction being validated. The contract's validator script uses the script context to check if the current time has passed the vesting deadline and if the transaction is signed by the beneficiary. This information is necessary to determine whether the conditions for releasing the vested funds have been met.

## Validator scripts
In a vesting contract, the validator script is responsible for enforcing the vesting conditions and ensuring that the funds are only released to the beneficiary after the specified deadline. The validator script takes the datum (vesting conditions) and the script context as inputs and uses this information to validate the transaction. If the current time is beyond the deadline and the transaction is signed by the beneficiary, the validator script allows the transaction to consume the vested funds. Otherwise, the transaction is deemed invalid, and the funds remain locked in the contract's UTxO.

# Writing your first Plutus smart contract

Now that you have a basic understanding of the core concepts, let's create a simple vesting contract. 

## Setting up a Plutus project
To set up a Plutus project for our vesting contract, follow these steps:

1. Create a new directory for your project and navigate to it in your terminal.

2. If you are using Nix, enter a Nix shell that provides the necessary development environment by running `nix develop` in your project directory. If you are not using Nix, make sure that all required C libraries are installed since PlutusTx depends on `cardano-base`, which in turn depends on cryptographic C libraries like `libblst`, `libsecp256k1`, and `libsodium`. 

3. Create a new directory named `src` and a new file named `MinLovelaceValidator.hs` inside it. This is where we'll write our smart contract code using Plutus Tx.

# First smart contract example

## Writing a simple Vesting contract

For this example, we will walk through a smart contract that is designed to use only very limited conditions. The contract provides for someone to send a gift of ada to a beneficiary. The beneficiary can access their gift only after a specific deadline has been passed and the beneficiary has signed the contract. 

## Overview 

### High-level conceptual stages of the vesting contract

| Stage | Description |
|-------|-------------|
| A. Initialization | Define the data structure and data types for the vesting contract, including the beneficiary's public key hash and the deadline for the vesting period. |
| B. Validation Logic | Create the logic that will validate transactions attempting to withdraw funds from the contract. |
| C. Validation Conditions | Establish the conditions under which the funds can be released, specifically that the current time is beyond the deadline and that the transaction is signed by the beneficiary. |
| D. Compilation | Wrap and compile the validation logic into a Plutus Validator type. |
| E. Helper Functions | Provide additional functions to save the compiled validator to a file and to print the vesting datum in JSON format for easy inspection. |

### Summarized list of the vesting contract's functionality section by section

1. Importing necessary modules and functions
2. On-chain / Validator code
   - Define the `VestingDatum` data type that holds the beneficiary's public key hash and the deadline for fund release.
   - Implement the core `mkVestingValidator` function that checks if the transaction is signed by the beneficiary and if the deadline has passed.
   - Wrap the validator function and compile it to a Validator type. `mkWrappedVestingValidator` is a wrapper for the validator function to conform to the expected type signature for Plutus validators. The compiled validator script ready for deployment on the blockchain.
3. Helper functions
   - `saveVal` is a helper function that saves and writes the validator script to a file. 
   - `printVestingDatumJSON` is a helper function to print the vesting datum in JSON format, given a public key hash and a deadline in ISO 8601 format.

### Section 1: Importing the required modules and functions

```haskell
{-# LANGUAGE DataKinds         #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell   #-}
 
module Vesting where

import           Data.Maybe                (fromJust)
import           Plutus.V1.Ledger.Interval (contains)
import           Plutus.V2.Ledger.Api      (BuiltinData, POSIXTime, 
                                            PubKeyHash,
                                            ScriptContext 
                                            (scriptContextTxInfo),
                                            TxInfo (txInfoValidRange),
                                            Validator, from, 
                                            mkValidatorScript)
import           Plutus.V2.Ledger.Contexts (txSignedBy)
import           PlutusTx                  (compile, unstableMakeIsData)
import           PlutusTx.Prelude          (Bool, traceIfFalse, ($), (&&))
import           Prelude                   (IO, String)
import           Utilities                 (Network, posixTimeFromIso8601,
                                            printDataToJSON,
                                            validatorAddressBech32, wrap,
                                            writeValidatorToFile)
```

- What would be useful to say here about general practices for importing modules and functions? 
- Add links to relevant module reference info


### Section 2.1: Defining the data type, public key hash, and deadline

```haskell
------------------------------------------------------------------------------
------------------------------ ON-CHAIN / VALIDATOR --------------------------

data VestingDatum = VestingDatum
    { beneficiary :: PubKeyHash
    , deadline    :: POSIXTime
    }

unstableMakeIsData ''VestingDatum
```

This next section defines the `VestingDatum` data type that holds the beneficiary's public key hash, `PubKeyHash`, and the deadline, `POSIXTime`, for releasing the funds. It generates the required instance for `VestingDatum`, allowing the `VestingDatum` type to be used in the validator script. 

### Section 2.2: Implementing the validator function

```haskell
{-# INLINABLE mkVestingValidator #-}
mkVestingValidator :: VestingDatum -> () -> ScriptContext -> Bool
mkVestingValidator dat () ctx = traceIfFalse "beneficiary's signature missing" signedByBeneficiary &&
                                traceIfFalse "deadline not reached" deadlineReached
  where
    info :: TxInfo
    info = scriptContextTxInfo ctx
 
    signedByBeneficiary :: Bool
    signedByBeneficiary = txSignedBy info $ beneficiary dat
 
    deadlineReached :: Bool
    deadlineReached = contains (from $ deadline dat) $ txInfoValidRange info
```

This section implements the core validator function, `mkVestingValidator`. It takes the `VestingDatum`, a unit value for the redeemer, and the `ScriptContext`. It returns a `Bool` that indicates whether the transaction is valid or not. 

The validation logic says that the funds can be unlocked only when the deadline has been reached and the transaction has been signed by the beneficiary. 

It extracts the transaction info from the script context and checks if the transaction is signed by the beneficiary, making sure that only the beneficiary can unlock the funds. Following that, it checks if the deadline has been reached, ensuring that the funds can be unlocked only after the specified deadline. 

In the validation code, we have the helper variables `signedByBeneficiary` and `deadlineReached` which are of type `Bool`. 

In the first variable, we use the helper function `txSignedBy` that takes in transaction info and a public key hash and checks whether this transaction has been signed with this public key hash. 

In the second variable, we access the validity range of the transaction and check that it is contained inside the interval starting with the deadline and going to infinity. 

### Section 2.3: Wrapping the validator function and compiling it to a Validator type

```haskell
{-# INLINABLE  mkWrappedVestingValidator #-}
mkWrappedVestingValidator :: BuiltinData -> BuiltinData -> BuiltinData -> ()
mkWrappedVestingValidator = wrap mkVestingValidator

validator :: Validator
validator = mkValidatorScript $$(compile [|| mkWrappedVestingValidator ||])
```

In this section, the code wraps the validator function, which is required by the Plutus compiler. 

Next, the wrapped validator function is compiled to a Validator type, creating a compiled version of the validator script that can be used in transactions. `mkWrappedVestingValidator` is a wrapper for the validator function to conform to the expected type signature for Plutus validators. 

The compiled validator script is ready for deployment on the blockchain. 

### Section 3: Saving the compiled validator script and printing VestingDatum in JSON format

```haskell
------------------------------------------------------------------------------
-------------------------------- HELPER FUNCTIONS ----------------------------

saveVal :: IO ()
saveVal = writeValidatorToFile "./assets/vesting.plutus" validator

printVestingDatumJSON :: PubKeyHash -> String -> IO ()
printVestingDatumJSON pkh time = printDataToJSON $ VestingDatum
    { beneficiary = pkh
    , deadline    = fromJust $ posixTimeFromIso8601 time
    }
```

These helper functions provide convenient ways to save the validator script to a file and print the `VestingDatum` in JSON format, which can be useful for testing and debugging purposes.

`saveVal` is a helper function that saves the compiled validator script to a file. It uses the `writeValidatorToFile` function from the `Utilities` module to write the compiled validator script to a file named "vesting.plutus" in the "./assets" directory.

The `printVestingDatumJSON` function is another helper function that takes the beneficiary's public key hash and the deadline as a string in ISO 8601 format. It constructs the `VestingDatum` using the provided values. The `fromJust` function is used to extract the `POSIXTime` value from the result of `posixTimeFromIso8601`. The `posixTimeFromIso8601` function converts the deadline string to a POSIXTime value. The constructed `VestingDatum` is then printed as JSON to the console using the `printDataToJSON` function.

If we run this function and input a date and time together with a public key hash, we get the following example output: 

```
Prelude> import Vesting
Prelude Vesting> :set -XOverloadedStrings
Prelude Vesting> import Plutus.V2.Ledger.Api
Prelude Vesting Plutus.V1.Ledger.Api> 
pkh1 = "cff6e39ec5b3cf84b1078976c98706b73774d2c5523af4daaf7c5109"
Prelude Vesting Plutus.V1.Ledger.Api>
printVestingDatumJSON pkh1 "2023-03-11T13:12:11.123Z"
{
	"constructor": 0,
	"fields": [
    		{
        	      "bytes": "cff6e39ec5b3cf84b1078976c98706b73774d2c5523af4daaf7c5109"
    		},
    		{
        	      "int": 1678540331123
    		}
	]
}
```

This datum can then be stored in a JSON file and later used in off-chain code. In the examples we have seen so far, we had one specific validator that was a Haskell value of type Validator. If there was any variability in the contract, we model that by using the datum as in the vesting example where the datum contained the beneficiary and the deadline. 

## Next steps

To put some context around this first contract example, let's talk about typical next steps that we would need to take to actually use this smart contract in the real world. 

Conceptually, we need to understand the following:
1. The vesting contract is designed to lock funds until a specified deadline has passed and only the designated beneficiary can unlock the funds.
2. The contract requires the beneficiary's public key hash and the deadline to be provided when creating the vesting datum.
3. The contract needs to be compiled and deployed on the Cardano blockchain.
4. The developer needs to interact with the deployed contract by sending transactions to lock funds and later unlock them.

On a high level, here are the general steps required to use this smart contract: 

1. Cardano node:
   - Set up a Cardano node and configure it to connect to the desired network (eg, testnet or mainnet).
   - The Plutus Pioneer Program describes how to interact with a Plutus smart contract using [Blockfrost](https://blockfrost.io/), a Cardano provider for indexing and querying the blockchain. If using Blockfrost, a developer does not need to run a Cardano node for themselves.

2. Compile the vesting contract:
   - Save the vesting contract code in a Haskell file (e.g., `Vesting.hs`).
   - Open a terminal and navigate to the directory containing the `Vesting.hs` file.
   - Run the `saveVal` function to compile the contract and save it as a `.plutus` file.

3. Deploy the vesting contract:
   - Use a Cardano wallet (eg, Lace, Nami, Eternl or Daedalus) to create a new wallet and obtain the wallet address.
   - Fund the wallet with some ada to cover transaction fees.
   - Use the Cardano CLI to create a transaction that deploys the compiled vesting contract to the blockchain.
   - Sign and submit the deployment transaction.

4. Interact with the vesting contract:
   - To lock funds in the vesting contract, create a transaction that sends ada to the contract address along with the vesting datum containing the beneficiary's public key hash and the deadline.
   - Use the `printVestingDatumJSON` function to generate the vesting datum in JSON format.
   - Sign and submit the transaction to lock the funds.
   - After the deadline has passed, the beneficiary can create a transaction to unlock the funds.
   - The transaction should reference the vesting contract address and provide the necessary input (the vesting datum) and the beneficiary's signature.
   - Sign and submit the transaction to unlock the funds and transfer them to the beneficiary's wallet.

5. Monitor and test:
   - Use Cardano explorer tools to monitor the transactions and the contract's state on the blockchain.
   - Test the contract thoroughly by locking funds, waiting for the deadline to pass, and unlocking the funds to ensure it behaves as expected.

6. Integration and deployment:
   - Integrate the vesting contract into a larger application or system if required.
   - Deploy the contract to the Cardano mainnet when ready for production use.

Remember to handle security aspects carefully, such as protecting private keys, properly validating inputs, and considering edge cases and potential vulnerabilities.

It's important to note that this is a simplified overview, and in practice, there may be additional steps and considerations depending on the specific requirements and tools used. It's recommended to refer to the Plutus documentation, tutorials, and examples provided by the Cardano community for more detailed guidance on developing and deploying Plutus smart contracts.

## Questions to address relating to testing and deploying smart contracts

*Questions for clarification:*

Luka Kurnjek is working on a book called _Mastering Cardano_. The chapter that focuses on Plutus security mentions the resources below. Are these resources still accurate and usable? Some of it relates to testing, some of it relates to basic definitions of concepts about what is Plutus, etc. 

- Testing is a complex topic that is probably beyond the scope of this onboarding and quick setup guide. Instead, I suggest we write a few sentences referring people to other resources. Luka has about 20 pages written up about testing Plutus scripts. 

- [Atlas](https://atlas-app.io/) is an application backend developed by GeniusYield and other companies. Lars is CTO of GeniusYield. Is it appropriate to refer readers to this resource instead of the PAB? 

- Does it make sense to refer developers to the Plutus application backend (PAB) tool? Is it still usable? 

- Is the MLabs [`plutus-simple-model`](https://github.com/mlabs-haskell/plutus-simple-model/tree/main) relevant for testing in the context of this first smart contract example? It talks about property tests. 

- Similar question for [`cooked-validators`](https://github.com/tweag/cooked-validators) by Tweag. 
   - "With `cooked-validators` you can test Cardano smart contracts (including Plutus v2 features) by writing potentially malicious offchain code. You can also use the library to write "normal" offchain code in a comfortable and flexible way."

- Is this video still accurate? [The Plutus platform](https://youtu.be/usMPt8KpBeI?si=X9uQsQQI4hjVv4KX)
   - It was recorded in July, 2020. I want to clarify which parts, if any, may no longer be true today. For example, does it depend on Plutus Tools? 

- Is this blog article still accurate? [Plutus Application Backend (PAB): supporting DApp development on Cardano](https://iohk.io/en/blog/posts/2021/10/28/plutus-application-backend-pab-supporting-dapp-development-on-cardano/)
   - Dated October, 2021

