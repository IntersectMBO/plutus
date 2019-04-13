# Multi-currency ledger

The blockchain simulator that backs the Playground has native support for user-defined currencies. This tutorial covers the Playground UI for entering and viewing amounts in currencies. For a detailed description of multi currency support on the ledger please refer to the [design document](../../docs/multi-currency/multi-currency.md).

## Known Currencies

Each currency on the ledger is identified by two 32-byte `ByteString`s. To make it easy to work with custom currencies in the Playground we have added a function `mkKnownCurrencies` (similar to `mkFunctions`). The argument to `mkKnownCurrencies` is a list of `KnownCurrency` values (exported from `Plutus.Playground`), which are defined as:

```haskell
data KnownCurrency = KnownCurrency
    { hash         :: ValidatorHash
    , friendlyName :: String
    , knownTokens  :: NonEmpty TokenId
    }
```

To define a `KnownCurrency` we need the `ValidatorHash` of the monetary policy script that controls the forging of the currency (see the [design document](../../docs/multi-currency/multi-currency.md) for details). `friendlyName` can be any `String` of your choice. Whenever a value of a currency is shown, we will see the currency's `friendlyName` instead of its `ValidatorHash`. `knownTokens` is a non-empty list of the currency's token IDs.

```haskell

myCurrency :: KnownCurrency
myCurrency = KnownCurrency  { ... }

$(mkKnownCurrency ['myCurrency])

```

*TODO: Actua example* 