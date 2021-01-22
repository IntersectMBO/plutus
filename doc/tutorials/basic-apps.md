::: {.highlight}
haskell
:::

Writing a basic Plutus app in the Plutus Playground {#basic_apps_tutorial}
===================================================

`Plutus apps<contract application>`{.interpreted-text role="term"} are
programs that run off-chain and manage active contract instances. They
monitor the blockchain, ask for user input, and submit transactions to
the blockchain. If you are a contract author, building a Plutus app is
the easiest way to create and spend Plutus script outputs. In this
tutorial we are going to write a Plutus app that locks some Ada in a
script output and splits them evenly between two recipients.

```haskell
import           Control.Monad             (void)
import           Data.Aeson                (FromJSON, ToJSON)
import qualified Data.Text                 as T
import           GHC.Generics              (Generic)
import           Language.Plutus.Contract
import qualified Language.PlutusTx         as PlutusTx
import           Language.PlutusTx.Prelude
import           Ledger
import qualified Ledger.Ada                as Ada
import qualified Ledger.Constraints        as Constraints
import qualified Ledger.Typed.Scripts      as Scripts
import           Schema
import           Wallet.Emulator.Wallet
```

Defining the types
------------------

We start by defining some data types that we\'re going to need for the
\_[Split]() app.

```haskell
data SplitData =
    SplitData
        { recipient1 :: PubKeyHash -- ^ First recipient of the funds
        , recipient2 :: PubKeyHash -- ^ Second recipient of the funds
        , amount     :: Ada -- ^ How much Ada we want to lock
        }
    deriving stock (Show, Generic)

PlutusTx.makeIsData ''SplitData
PlutusTx.makeLift ''SplitData
```

`SplitData` describes the two recipients of the funds, and the total
amount of the funds denoted in Ada.

We are using the `PubKeyHash` type to identify the recipients. When
making the payment we can use the hashes to create two public key
outputs.

### Instances for data types

The `SplitData` type has instances for a number of typeclasses. These
instances enable the serialisation of `SplitData` to different formats.
`ToJSON` and `FromJSON` are needed for JSON serialisation. JSON objects
are passed between the frontend (for example, the Playground) and the
app instance. `Language.PlutusTx.IsData`{.interpreted-text role="hsobj"}
is used for values that are attached to transactions, for example as the
\<redeemer\> of a script output. This class is used by the Plutus app at
runtime to construct `Data` values. Finally,
`Language.PlutusTx.makeLift`{.interpreted-text role="hsobj"} is a
Template Haskell statement that generates an instance of the
`Language.PlutusTx.Lift.Class.Lift`{.interpreted-text role="hsobj"}
class for `SplitValue`. This class is used by the Plutus compiler at
compile-time to construct Plutus core programs.

Defining the validator script
-----------------------------

The validator script is the on-chain part of our Plutus app. The job of
the validator is to look at individual transactions in isolation and
decide whether they are valid. Plutus validators have the following type
signature:

``` {.haskell}
d -> r -> ValidatorCtx -> Bool
```

where `d` is the type of the \<datum\> and `r` is the type of the
redeemer.

We are going to use the validator script to lock a script output that
contains the `amount` specified in the `SplitData`.

::: {.note}
::: {.admonition-title}
Note
:::

There is an n-to-n relationship between Plutus apps and validator
scripts. Apps can deal with multiple validators, and validators can be
used by different apps.
:::

In this tutorial we only need a single validator. Its datum type is
`SplitData` and its redeemer type is `()` (the unit type). The validator
looks at the `ValidatorCtx` value to see if the conditions for making
the payment are met:

```haskell
validateSplit :: SplitData -> () -> ValidatorCtx -> Bool
validateSplit SplitData{recipient1, recipient2, amount} _ ValidatorCtx{valCtxTxInfo} =
    let half = Ada.divide amount 2 in
    Ada.fromValue (valuePaidTo valCtxTxInfo recipient1) >= half &&
    Ada.fromValue (valuePaidTo valCtxTxInfo recipient2) >= (amount - half)
```

The validator checks that the transaction, represented by
`valCtxTxInfo`, pays half the specified amount to each recipient.

We then need some boilerplate to compile the validator to a Plutus
script (see `basic_validators_tutorial`{.interpreted-text role="ref"}).

```haskell
data Split
instance Scripts.ScriptType Split where
    type instance RedeemerType Split = ()
    type instance DatumType Split = SplitData

splitInstance :: Scripts.ScriptInstance Split
splitInstance = Scripts.validator @Split
    $$(PlutusTx.compile [|| validateSplit ||])
    $$(PlutusTx.compile [|| wrap ||]) where
        wrap = Scripts.wrapValidator @SplitData @()
```

The `ScriptType` class defines the types of the validator, and
`splitInstance` contains the compiled Plutus core code of
`validateSplit`.

Asking for input
----------------

When we start the app, we want to ask the sender for a `SplitData`
object. In Plutus apps, the mechanism for requesting inputs is called
`endpoints <endpoint>`{.interpreted-text role="term"}.

All endpoints that an app wants to use must be declared as part of the
type of the app. The set of all endpoints of an app is called the
`schema`{.interpreted-text role="term"} of the app. The schema is
defined as a Haskell type. We can build a schema using the `Endpoint`
type family to construct individual endpoint types, and the `.\/`
operator to combine them.

```haskell
data LockArgs =
        LockArgs
            { recipient1Wallet :: Wallet
            , recipient2Wallet :: Wallet
            , totalAda         :: Ada
            }
    deriving stock (Show, Generic)
    deriving anyclass (ToJSON, FromJSON, ToSchema)

type SplitSchema =
    BlockchainActions
        .\/ Endpoint "lock" LockArgs
        .\/ Endpoint "unlock" LockArgs
```

The `SplitSchema` defines two endpoints, `lock` and `unlock`. Each
endpoint declaration contains the endpoint\'s name and its type. Note
that `SplitData` has two `PubKeyHash` fields for the recipients, whereas
the endpoint has two `Wallet` fields (the wallet type is used in the
Playground as the identity of a simulated agent). We are going to
convert the wallet values to their corresponding public key hashes in
the `Split` app. That way, the user can simply identify the recipient by
a number and doesn\'t have to enter a public key into a text box. This
type of conversion from a nickname to a unique identifier is a common
task for Plutus apps.

To use the `lock` endpoint in our app, we call the
`Language.Plutus.Contract.Effects.ExposeEndpoint.endpoint`{.interpreted-text
role="hsobj"} function:

```haskell
lock :: Contract SplitSchema T.Text LockArgs
lock = endpoint @"lock"

unlock :: Contract SplitSchema T.Text LockArgs
unlock = endpoint @"unlock"
```

`endpoint` has a single argument, the name of the endpoint. The name of
the endpoint is a Haskell type, not a value, and we have to supply this
argument using the type application operator `@`. This operator is
provided by the
[TypeApplications](https://gitlab.haskell.org/ghc/ghc/-/wikis/type-application)
GHC extension.

Next we need to turn the two `Wallet` values into their public key
hashes so that we can get the `SplitData` value from the input that was
supplied by the user.

```haskell
mkSplitData :: LockArgs -> SplitData
mkSplitData LockArgs{recipient1Wallet, recipient2Wallet, totalAda} =
    let convert :: Wallet -> PubKeyHash
        convert = pubKeyHash . walletPubKey
    in
    SplitData
        { recipient1 = convert recipient1Wallet
        , recipient2 = convert recipient2Wallet
        , amount = totalAda
        }
```

Note that the `Wallet.Emulator.Wallet.walletPubKey`{.interpreted-text
role="hsobj"} function and the
`Wallet.Emulator.Wallet.Wallet`{.interpreted-text role="hsobj"} type are
only available in the simulated environment used by the Plutus
playground and by Plutus tests. A real Plutus app would use the metadata
server or a custom lookup function for such conversions.

Locking the funds
-----------------

With the `SplitData` that we got from the user we can now write a
transaction that locks the requested amount of Ada in a script output.

```haskell
lockFunds :: SplitData -> Contract SplitSchema T.Text ()
lockFunds s@SplitData{amount} = do
    logInfo $ "Locking " <> show amount
    let tx = Constraints.mustPayToTheScript s (Ada.toValue amount)
    void $ submitTxConstraints splitInstance tx
```

Using the constraints library that comes with the Plutus SDK we specify
a transaction `tx` in a single line.

``` {.haskell}
tx = Constraints.mustPayToTheScript s (Ada.toValue amount)
```

After calling `submitTxConstraints` in the next line, the Plutus app
runtime examines the transaction constraints `tx` and builds a
transaction that fulfills them. The runtime then sends the transaction
to the wallet, which adds enough to cover the required funds (in this
case, the ada amount specified in `amount`).

Unlocking the funds
-------------------

All that\'s missing now is the code for retrieving the funds, and some
glue to put it all together.

```haskell
unlockFunds :: SplitData -> Contract SplitSchema T.Text ()
unlockFunds SplitData{recipient1, recipient2, amount} = do
    let contractAddress = (Ledger.scriptAddress (Scripts.validatorScript splitInstance))
    utxos <- utxoAt contractAddress
    let half = Ada.divide amount 2
        tx =
            collectFromScript utxos ()
            <> Constraints.mustPayToPubKey recipient1 (Ada.toValue half)
            <> Constraints.mustPayToPubKey recipient2 (Ada.toValue $ amount - half)
    void $ submitTxConstraintsSpending splitInstance utxos tx
```

In `unlockFunds` we use the constraints library to build the spending
transaction. Here, `tx` combines three different constraints.
`collectFromScript` takes the script outputs in `unspentOutputs` and
adds them as input to the transaction, using the unit `()` as the
redeemer. The other two constraints use `mustPayToPubKey` to add
payments for the recipients.

Deploying the app on the Playground
-----------------------------------

We have all the functions we need for the on-chain and off-chain parts
of the app. Every contract in the Playground must define its public
interface like this:

```haskell
endpoints :: Contract SplitSchema T.Text ()
```

The Playground server uses the `endpoints` definition to populate the UI
(via the schema, in our case `SplitSchema`) and to start the simulation.
`endpoints` is the high-level definition of our app:

```haskell
endpoints = (lock >>= lockFunds . mkSplitData) `select` (unlock >>= unlockFunds . mkSplitData)
```

The `select` function acts like a choice between two branches. The left
branch starts with `lock` and the right branch starts with `unlock`. The
app exposes both endpoints and proceeds with the branch that receives an
answer first. So, if we call the `lock` endpoint in one of the simulated
wallets, it will call `lockFunds` and ignore the `unlock` side of the
contract.

We also need a couple of declarations that generate glue code for the
Playground.

``` {.haskell}
mkSchemaDefinitions ''SplitSchema

$(mkKnownCurrencies [])
```

And an additional import at the top of the file.

``` {.haskell}
import Playground.Contract
```

After that, we can compile the contract and create a simulation. The
following action sequence results in two transactions that lock the
funds and then distribute them to the two recipients.

![Simulation for the split
app.](images/playground-basic-app-simulation.png)

Exercise
--------

1.  Extract the function that assigns funds to each recipient from
    `unlockFunds` and `validateSplit` to reduce redundancy in the code
2.  Extend the contract to deal with a list of recipients instead of a
    fixed number of 2.
