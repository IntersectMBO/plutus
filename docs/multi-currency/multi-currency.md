# Multi-currency on the UTXO Ledger

## Summary

* We currently have the model in "An Abstract Model of UTxO-based Cryptocurrencies with Scripts" [1], with modifications to the transaction data type and to the transaction validation function (see section "Current State"). We now want to add support for user-issued currencies and tokens to the ledger
* The approach in "Multi-Currency Ledger" [2] introduces additional global state in form of a registry of known currencies
* We propose a different solution that uses the UTXO set and pay-to-script outputs to forge value, allowing for a light-weight implementation of user-defined currencies

## Current State

We have implemented a blockchain emulator (mockchain) as a Haskell library. An important feature of the mockchain is that it faithfully emulates the behaviour of Plutus smart contracts in a UTXO-style ledger, by storing, deserialising and running Plutus scripts the same way they will be run when Plutus is integrated with the Cardano blockchain. 

The mockchain is implemented in the [Wallet.Emulator.Types](../../wallet-api/src/Wallet/Emulator/Types.hs) module. The data types are defined in [Ledger.Types](../../wallet-api/src/Ledger/Types.hs) and the transaction validation rules are implemented in [Ledger.Index](../../wallet-api/src/Ledger/Index.hs). 

The mockchain extends the model described in [1] in two ways, by adding data scripts to pay-to-script outputs, and by adding a validity range to transactions. We provide a brief summary here. More details can be found in [this document](../extended-utxo/README.md).

The mockchain uses the following data type for transactions:

```haskell

-- | Transaction including witnesses for its inputs
data Tx = Tx {
    txInputs     :: Set.Set TxIn,
    txOutputs    :: [TxOut],
    txForge      :: !Value,
    txFee        :: !Ada,
    txValidRange :: !SlotRange
    }
```

Note the `txValidRange` field. This field contains an interval of slot numbers during which the transaction may be validated. The value of a transaction's `txValidRange` is passed to any validator scripts that are run during validation of that transaction's inputs, in order to make Plutus scripts deterministic. See [here](https://github.com/input-output-hk/fm-ledger-rules/issues/139) for the planned work to integrate this into the formal ledger rules for the Shelley release. The `SlotRange` type is defined in [`Ledger.Interval`](../../wallet-api/src/Ledger/Interval.hs).

The `Value` and `Ada` types represent currency in the mockchain. `Ada` is the designated currency in which fees are paid, and `Value` a map of currency identifiers to quantities, following Def. 1 in [2]. 

### Scripts

In [1], scripts are defined as an abstract type `Script` with a single operation `evaluate`. The mockchain defines `Script` in [`Ledger.Types`](../../wallet-api/src/Ledger/Types.hs), and `evaluate` as `runScript` in the same module.

The function `s` [1, Def. 13], providing information about the current state of the ledger and the pending transaction, is implemented essentially as "lifting" a value of `Tx` from Haskell to its PLC representation. The PLC representation of `Tx` is called `PendingTx` and can be found in the [`Ledger.Validation`](../../wallet-api/src/Ledger/Validation.hs) module.

### Transaction inputs and outputs

`TxIn` and `TxOut` are defined in [`Ledger.Types`](../../wallet-api/src/Ledger/Types.hs). For this proposal we will use the following (simplified) types.

```haskell

data TxOut = 
  PayToPubKey PubKey Value
  | PayToScript ScriptHash DataScript Value

data TxOutRef = TxOutRef { txOutRefId :: TxHash, txOutRefIndex :: Int }

data TxIn =
  ConsumeScriptAddress TxOutRef ValidatorScript RedeemerScript 
  | ConsumePublicKeyAddress TxOutRef Signature

```

Every `TxIn` refers to a unique `TxOut` via `TxOutRef`, and when we talk about the value of a `TxIn` we mean the value the `TxOut` it points to.

### Ledger Rules

The ledger rules are a set of conditions that need to hold for a transaction to be considered valid in a given ledger. The following rules are important for this proposal. In the current (single-currency) ledger we have:

1. **(balanced)** The sum of the values of the `txInputs` field plus the `txForge` value must be equal to the sum of the values of the `txOutputs` field plus the `txFee` field.
2. **(forging)** A transaction with a non-zero `txForge` field is only valid if the ledger is empty (that is, if it is the initial transaction). Note that the details of this rule depend on the monetary policy of the ledger itself, as there may be other transactions that forge value.
3. **(legitimacy)** Every transaction must prove that it is allowed to spend the inputs. To spend a `PayToPubKey` transaction output, the signature provided in `ConsumePublicKeyAddress` must match the public key. For a `PayToScript` transaction output, the hash of the `ConsumeScriptAddress` input's `ValidatorScript` must be equal to the output's `ScriptHash`, and evaluation of the `ValidatorScript` applied to the output's `DataScript`, the input's `RedeemerScript` and the `PendingTx` value of the spending transaction must finish successfully.
4. **(no double spending)** Every transaction output may be spent at most once. That is, a `Tx` is only valid if none of the `TxOut` values referred to by its `txInputs` field has been spent by a transaction already in the ledger.

For details of the implementation of the ledger rules please refer to `validateTransaction` in [`Ledger.Index`](../../wallet-api/src/Ledger/Index.hs).

## Problem

The `Value` type used in transactions has been introduced in preparation for the multi-currency ledger. This is only one half of adding multi-currency support at the ledger level because we still need a way to actually generate (forge) values of new currencies. 

To enable the forging of currency value, the paper [2] envisages a new type of transaction called `CurrencyTx` (see [2, Def. 2]). `CurrencyTx` creates a new *known currency*, by registering the currency's name as a unique (across the ledger) string, and associating it with a `Script` representing the monetary policy for that currency. 

Adding the `CurrencyTx` type results in additional work for core nodes: They need to keep track of the name and monetary policy of every currency that has ever been created. So `CurrencyTx` adds a new kind of ledger-wide, global state (in addition to the UTXO set), in form of the registry of currencies and their policies. Unlike the UTXO set this new global state can only ever grow larger, because there is no way to destroy a currency. While at the moment neither the cost model of regular UTXO-with-script transactions nor that of `CurrencyTx` transactions has been developed, it seems likely that the cost of a `CurrencyTx` is going to be higher than the effect an added `PayToScript` output has on the cost of a regular transaction. 

This makes multi-currency based on the `CurrencyTx` proposal potentially unsuitable for applications that require lightweight currencies, in particular the implementation of [Non-Fungible Tokens](https://eips.ethereum.org/EIPS/eip-721) (NFTs).

## Proposed solution

We propose a new extension to the UTXO model with scripts, an extension that has the same effects as adding a `CurrencyTx` transaction type (namely, the ability to forge value of user-defined currencies) but without the added overhead of a currency registry.

The proposal consists of two changes.

1. Instead of using a `String` value to identify a currency, we use the `ScriptHash` type (a ByteString)
2. We replace the **(forging)** rule above with the following rule: **(forging2)** A transaction with a non-zero `txForge` field is only valid if for every key `h` in `txForge`, the transaction's set of inputs `txIn` contains a `TxIn` that spends a `TxOut` whose address is `h`.

The **(forging2)** rule, together with the **(legitimacy)** rule, ensures that the script `H` (with hash `h`) is run whenever new value of the currency `h` is forged. Because `H` is provided with the `txForge` field of the spending transaction, via the `PendingTx` type, it can block or authorise any amount of value that is created of its currency. There is no need for a registry of currencies because the thing that identifies a currency is (the hash of) its monetary policy.

With this proposal a custom currency is no different from any other smart contract, and currencies don't require a separate cost model.

We can write monetary policy as a state machine that keeps track of the current supply and forges more value when necessary.

By allowing values in the `txForge` field to be negative, we can reduce the supply of a currency. 

## Example (creating a currency)

To illustrate the approach, suppose we have written a validator script `H` that controls the monetary policy of our new currency. To forge a value of `hash(H)`, we need two transactions.

1. `tx1` produces an `o :: TxOut` that is locked with a ByteString  `h = hash(H)`. The `txForge` field of `tx1` is zero.
2. `tx2` consumes the `TxOut` produced by `tx1`. Its `txForge` field has an entry `{ h -> 1000 }`, so `tx2` forges 1000 units of our currency. For `tx2` to be valid, the `TxIn` that refers to `o` must provide the validator script (ie. the monetary policy) `H` and an appropriate redeemer. The outputs of `tx2` contain (among others) 1000 units of the `h`, which can be spent freely from now on, without referring to the script `H`. `o` is removed from the UTXO set when `tx2` is added to the ledger.

## Example (NFT)

An important example that motivated the search for an alternative to the `CurrencyTx` approach was the idea to implement NFTs as currencies with a supply of 1. If NFTs are used to represent different stakes in a contract, then a single instance of a contract requires multiple NFTs, so it is crucial that currency creation is as lightweight as possible. In our proposal, each NFT adds a single pay-to-script transaction output to the initial transaction of the contract, and  does not otherwise put a burden on core nodes.

Here is an example of a validator script that implements a non-fungible token using our proposal.

```haskell
data NFT = NFT { nftName :: String, nftBootstrapTxOut :: TxOutput } 

-- the validator script (in reality this would be a quoted TH expression)
 nftValidator :: NFT -> Data -> Redeemer -> PendingTx -> () 
 nftValidator (NFT nm txout) _ _ ptx = 
  let con1 = ptx `spends` txout 
      con2 = ptx `forges` 1 (ownAdress ptx) 
  in if con1 && con2 then () else error
```

`spends :: PendingTx -> TxOut -> Bool` checks if the pending transaction spends the tx output (uniquely identified by transaction hash + index into its list of outputs). `forges :: PendingTx -> Int -> ByteString -> Bool` checks if the pending transaction forges the given amount of the address. `Data` and `Redeemer` are the types (in PLC) of the data and redeemer scripts, which we ignore here (so effectively `type Data = ()` and `type Redeemer = ()`). For an actual currency we could the data script to keep track of the current supply.

Note that the validator script for a given `NFT` definition is given by `nftValidator nft`, so its address is the hash of `nftValidator nft`.

The key is the `nftBootstrapTxOut` field. Condition `con1` ensures that there is only a single transaction that can forge a value of the NFT, because `txout` can only be spent once, thanks to the **(no-double-spending rule)**. Condition `con2` ensures that only a single token of the currency is created, effectively making it non-fungible.

It is of course possible to produce multiple script outputs to the same address of `nftValidator nft` but only one of them can be spent, because the referenced tx output can only be spent once.

## References

[1] "An Abstract Model of UTxO-based Cryptocurrencies with Scripts"
[2] "Multi-Currency Ledger"