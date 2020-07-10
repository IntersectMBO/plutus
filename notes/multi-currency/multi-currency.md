# Multi-currency on the UTXO Ledger

## Summary

* We currently have the model in "An Abstract Model of UTxO-based Cryptocurrencies with Scripts" [1], with modifications to the transaction data type and to the transaction validation function (see section "Current State"). We now want to add support for user-issued currencies and tokens to the ledger
* The approach in "Multi-Currency Ledger" [2] introduces additional global state in form of a registry of known currencies
* We propose a different solution that uses the UTXO set and pay-to-script outputs to forge value, allowing for a light-weight implementation of user-defined currencies

## Current State

We have implemented a blockchain emulator (mockchain) as a Haskell library. An important feature of the mockchain is that it faithfully emulates the behaviour of Plutus smart contracts in a UTXO-style ledger, by storing, deserialising and running Plutus scripts the same way they will be run when Plutus is integrated with the Cardano blockchain.

The mockchain is implemented in the [Wallet.Emulator.Types](../../wallet-api/src/Wallet/Emulator/Types.hs) module. The data types are exposed in [Ledger](../../wallet-api/src/Ledger.hs) and the transaction validation rules are implemented in [Ledger.Index](../../wallet-api/src/Ledger/Index.hs).

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

In [1], scripts are defined as an abstract type `Script` with a single operation `evaluate`. The mockchain defines `Script` in [`Ledger.Scripts`](../../wallet-api/src/Ledger/Scripts.hs), and `evaluate` as `runScript` in the same module.

The function `s` [1, Def. 13], providing information about the current state of the ledger and the pending transaction, is implemented essentially as "lifting" a value of `Tx` from Haskell to its PLC representation. The PLC representation of `Tx` is called `PendingTx` and can be found in the [`Ledger.Validation`](../../wallet-api/src/Ledger/Validation.hs) module.

### Transaction inputs and outputs

`TxIn` and `TxOut` are defined in [`Ledger.Tx`](../../wallet-api/src/Ledger/Tx.hs). For this proposal we will use the following (simplified) types.

```haskell

data TxOut =
  PayToPubKey PubKey Value
  | PayToScript ScriptHash DataValue Value

data TxOutRef = TxOutRef { txOutRefId :: TxHash, txOutRefIndex :: Int }

data TxIn =
  ConsumeScriptAddress TxOutRef Validator RedeemerValue
  | ConsumePublicKeyAddress TxOutRef Signature

```

Every `TxIn` refers to a unique `TxOut` via `TxOutRef`, and when we talk about the value of a `TxIn` we mean the value the `TxOut` it points to.

### Ledger Rules

The ledger rules are a set of conditions that need to hold for a transaction to be considered valid in a given ledger. The following rules are important for this proposal. In the current (single-currency) ledger we have:

1. **(balanced)** The sum of the values of the `txInputs` field plus the `txForge` value must be equal to the sum of the values of the `txOutputs` field plus the `txFee` field.
2. **(forging)** A transaction with a non-zero `txForge` field is only valid if the ledger is empty (that is, if it is the initial transaction). Note that the details of this rule depend on the monetary policy of the ledger itself, as there may be other transactions that forge value.
3. **(legitimacy)** Every transaction must prove that it is allowed to spend the inputs. To spend a `PayToPubKey` transaction output, the signature provided in `ConsumePublicKeyAddress` must match the public key. For a `PayToScript` transaction output, the hash of the `ConsumeScriptAddress` input's `Validator` must be equal to the output's `ScriptHash`, and evaluation of the `Validator` applied to the output's `DataValue`, the input's `RedeemerValue` and the `PendingTx` value of the spending transaction must finish successfully.
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

Note that creating an NFT with this contract requires three transactions: One for the `nftBootstrapTxOut` transaction output, one for producing an output to the NFT address, and one that forges the token, consuming the output from the NFT address and the `nftBootstrapTxOut`. Note that the bootstrap transaction output can be any unspent transaction output owned by us, in particular it can be the same output that pays the fees for the forging transaction.

## Example (Currency with monetary policy)

The following contract implements a monetary policy of a currency `c` that can be forged repeatedly, up to a predefined maximum amount.

We use the data script to keep track of how much `c` has been issued so far. However, when authorising the forging of new `c` (that is, when running the validator script whose hash is `c`) we cannot verify that the data script we received contains the correct amount of `c` in circulation, because anyone can produce a pay-to-script transaction output locked by `c` and with an arbitrary data script. To prevent this kind of unauthorised forging of `c` we use a *reserve currency*, `c*`. This reserve currency represents the potential amount of `c` that can still be forged. Whenever we increase the supply of `c`, we destroy the same amount of `c*` and vice versa. The total circulation of `c` plus the total supply of `c*` equals the maximum supply of `c` at all times. To legitimise the forging of `c` we require the forger to present the entire amount of `c*` that exists.

We can think of `c` as paper notes and `c*` as a gold bar that we keep in our vault. Every unit of `c` is a claim to some of our gold bar. We can trade this claim away but we always keep the gold (although now the amount of gold that is available is smaller).

See below the script for an example.

```haskell

data CurRole = ActualCurrency | ReserveCurrency

newtype Currency = Currency {
    curMaxCirculation :: Int,
    -- ^ Maximum amount of currency that can be forged
    curRole :: CurRole,
    -- ^ Which of the two currencies (c or c*) lives at this address
    curBootstrapTxOut :: TxOut
    -- ^ Transaction output for initialising the currency
  }

-- | Current state of the state machine
newtype CurState =
  InitialState
  -- ^ Initial state, the reserve currency has not been forged
  | Circulating {
      csCurrentSupply :: Int,
      -- ^ How much of c has been issued
      csReserveAddr :: ByteString,
      -- ^ Identifier of the reserve currency
      csCurAddr    :: ByteString
      -- ^ Identifier of the currency itself
      }

-- | State machine input
data CurAction =
  Initialise { caReserve :: ByteString, caActual :: ByteString }
  | CurForge { cfForge :: Int }

-- | Data needed to verify a change in the circulation of the currency
--   (forging or destroying value)
data CirculationChange = CirculationChange {
    ccReserveAddr        :: ByteString,
    -- ^ Address of the reserve currency
    ccCurAddr            :: ByteString,
    -- ^ Address of the currency itself
    ccCurrentSupply      :: Int,
    -- ^ How much of the currency has already been forged
    ccForge              :: Int
    -- ^ How much we want to forge (can be negative)
  }

-- | Create the validator script for a `Currency`.
currencyScript :: Currency -> Validator
currencyScript cur = Validator val where
  val = Ledger.applyScript inner (Ledger.lifted cur)
  inner = $$(Ledger.compileScript [|| \(Currency maxCirc role txout) ->
    let

      -- Check whether a transaction (PendingTx) that changes the supply of c
      -- and c* preserves the invariant of "supply(c) + supply(c*) = maxSupply",
      -- and produces the entire amount of c* that is left.
      balancesOk :: CirculationChange -> PendingTx -> Bool
      balancesOk (CirculationChange reserveAddr curAdr currentCirc forged) ptx =
        let newCirc = currentCirc + forged
        in
             -- the required amount of c is forged by ptx
             ptx `forges` forged curAdr

             -- the same amount of c* is destroyed
          && ptx `forges` (negate forged) reserveAddr

             -- ptx produces the entire remaining amount of c*
          && ptx `outputs` (maxCirc - newCirc) reserveAddr

      -- A state machine for the reserve currency, c*.
      -- In the initial state we verify the transaction forges an amount of
      -- c* equal to `maxCirc`, and 0 of c. We also check that the script addresses
      -- from the `Initialise` argument match those of the pending transaction.
      -- In all other states we check that the action preserves the currency invariant.
      reserveStateMachine :: CurState -> CurAction -> PendingTx -> CurState
      reserveStateMachine InitialState (Initialise reserve actual) ptx =
        if
             ptx `forges` 0 actual
          && ptx `forges`  maxCirc (ownAddress ptx)
          && ptx `spends` txout
          && addressEq reserve (ownAddress ptx)
          && ptx `spendsFrom` actual
        then Circulating 0 reserve actual
        else $$(P.error)
      reserveStateMachine (Circulating currentCirc reserveAdr curAdr) (CurForge forged) ptx =
        if balancesOk (CirculationChange reserveAdr curAdr currentCirc forged)
           && addressEq reserveAdr (ownAddress ptx)
        then Circulating newCirc actualCur
        else $$(P.error)

      -- A state machine for the actual currency, c.
      -- In the initial state we verify the transaction forges an amount of
      -- c* equal to `maxCirc`, and 0 of c. We also check that the script addresses
      -- from the `Initialise` argument match those of the pending transaction.
      -- In all other states we check that the action preserves the currency
      -- invariant.
      currencyStateMachine :: CurState -> CurAction -> PendingTx -> CurState
      currencyStateMachine InitialState (Initialise reserve actual) ptx =
        if
             ptx `forges` 0 (ownAddress ptx)
          && ptx `forges`  maxCirc reserve
          && ptx `spends` txout
          && addressEq actual (ownAddress ptx)
        then Circulating 0 reserve actual
        else $$(P.error)
      currencyStateMachine (Circulating currentCirc reserveAdr curAdr) (CurForge forged) ptx =
        if balancesOk (CirculationChange reserveAdr curAdr currentCirc forged)
           && addressEq curAdr (ownAddress ptx)
        then Circulating newCirc actualCur
        else $$(P.error)

    in
      case role of
        ActualCurrency -> $$(P.mkStateMachine) currencyStateMachine
        MirrorCurrency -> $$(P.mkStateMachine) reserveStateMachine

    ||]
```

#### Transactions

To create a new currency with a maximum supply of 10000 and an initial supply of 100 we need to do the following. Steps 1-4 cover the initial setup and are only needed once. Step 5 demonstrates a regular interaction with the currency (changing its supply).

1. Select an unspent transaction output `txout` owned by us
2. Define `dsCur :: Validator, dsReserve :: Validator` with `dsCur = currencyScript (Currency 10000 ActualCurrency txout)` and `dsReserve = currencyScript (Currency 10000 MirrorCurrency txout)`. Their hashes are `hCur :: ByteString = hash dsCur` and `hRes :: ByteString = hash dsReserve`. `hCur` identifies the new currency, and `hRes` identifies its reserve currency.
3. Create a transaction `tx1`. `tx1` produces two pay-to-script outputs: `cur1` and `res1`. The address of `cur1` is `hCur`. The address of `res1` is `hRes`. `cur1` and `res1` have the same data script, `(InitialState, Initialise hRes hCur)` (see below for an explanation of the (state, action) tuples in data and redeemer scripts). The `valueForged` field of `tx1` is empty.
4. Create a transaction `tx2`. `tx2` spends `cur1` and `res1`, using the redeemer `r = (Circulating hRes hCur 0, Initialise hRes hCur)` for both outputs. `tx2` also spends `txout` and potentially other outputs that are needed to cover the fee. `tx2` produces pay-to-script outputs `cur2` and `res2`. The address of `cur2` is `hCur` and the address of `res2` is `hRes`. The outputs `cur2` and `res2` have the same data script: `r`, and their value is zero. In addition `tx2` produces an output `o` of `10000 hRes` to a pubkey address owned by us. The `valueForged` field of `tx2` is `{ hResror -> 10000 }`.
5. To issue `100 hCur` currency, create a transaction `tx3`. `tx3` spends `o` as well as `cur2` and `res2`, using the redeemer `r = (Circulating hRes hCur 100, Forge 100)`. `tx3` produces outputs `cur3` and `res3` to the addresses `hCur` and `hRes` respectively, using the data script `r`. In addition, `tx3` produces an output `p` with a value of `100 hCur`, and an output `q` with a value of `9900 hRes`. The address of `q` is a public key address owned by us. The address of `p` can be any public key or script address (wherever we want to send the new currency). The `valueForged` field of `tx3` is `{ hRes -> -100, hCur -> 100 }`.

The reason why the data and redeemer scripts used in steps 2-5 are of the form `(state, input)` is that this is currently the only way we have of [validating the next data script](https://github.com/input-output-hk/plutus/issues/426). The linked github issue explains the encoding under the heading "Possible Solutions", third item.

#### A different monetary policy

Suppose we wanted define a currency with a variable maximum supply, for example bound to interest rate. We can use the same pattern (reserve currency), we just need to change the `reserveStateMachine` function to allow transactions that forge the reserve currency without destroying the same amount of the actual currency at the same time.

# Native NFT support

Ethereum has support for so-called "non-fungible tokens" (NFTs). These have been
wildly popular, as they are useful for representing items with distinct
identities.

We would also like to support these. We might be able to encode them using the
multi-currency support described above, but we could also implement support for
them directly. This proposal is compatible with either the multi-currency
proposal above or the one in [2].

## Generalizing Value

This proposal suggests a change to the `Value` type used above and in [2], which
supports both fungible and non-fungible tokens, with no need to change any of
the other ledger rules.

The new definition of `Value` is:

```
type Value = Map CurrencyId (Map Token Quantity)
```

where:
- `CurrencyId` is the type we are using to identify currencies, either `String`
  in [2] or `ScriptHash` above.
- `Token` is an identifier for an individual token, probably a hash.
- `Quantity` is a type used to measure the amount of a token that is present.
  [2] and above use `Int`, but the ledger rules only require that it be a
  monoid with equality.

The ledger rules talk about *comparing* and *summing* values, so we must define
those operations for our `Value` type. In this case they are simply defined pointwise.

## Ledger rules

The ledger rules remain the same. In particular:

- The **(balanced)** rule now states that the quantity of each token on each
  side must be equal.
- If we are adopting the earlier proposal, the **(forging2)** rule does not need to change since
  it only talks about the keys of the value, which are still `CurrencyId`s.

Of course, the implementation of the ledger rules will change, because we have
changed what `Value`s are and what addition of `Value`s means, but at a logical
level they are unchanged.

## Implications

This model allows us to implement fungible (normal) and non-fungible token currencies, as well as
"mixed states":
- Fungible token currencies are implemented by only ever issuing
  `Quantity`s of a single `Token`.
- Non-fungible token currencies are implemented by only ever issuing unit
  `Quantity`s of many unique `Token`s.
    - Note that there is nothing in this proposal which enforces uniqueness:
      having multiples of a single `Token` merely means that those can be used
      fungibly. If a currency wants to make sure it only issues unique tokens it
      must track this itself.
- "Mixed" token currencies can have many `Token`s, but these can have more than
  unit `Quantity` in circulation.
    - These can be useful to model distinct categories of thing where there are
      fungible quantities within those, e.g. share classes.

## Performance

Care must be taken to ensure that we don't make transactions which only use Ada
significantly less efficient. This could be accomplished by adding specialized
cases to `Value`, e.g.:
```
data Value = SingleTokenQuantity CurrencyId Token Quantity
           | Map CurrencyId (Map Token Quantity)
```

Thus in the normal case we would only add:
- a case discrimination (needed to special-case any multi-currency value type)
- a check that the currency id matches (needed in any multi-currency proposal)
- a check that the token id matches (a new cost)

This seems like an acceptable overhead.

A more significant cost may be that we can no longer use `{-# UNPACK #-}` when
our `Value` type stops being a simple combination of wrappers and products
around primitives, but this is again an issue with any multi-currency proposal.

## Further generalizations

Nothing here requires that `Quantity` be anything more than an arbitrary monoid.
However, we gain something if we require it to be a group: inverses. That means
that we can destroy tokens, which may well be desirable.

# References

[1] "An Abstract Model of UTxO-based Cryptocurrencies with Scripts"
[2] "Multi-Currency Ledger"
