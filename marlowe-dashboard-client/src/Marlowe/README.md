# About Marlowe Contracts and the PAB

"Contract" in the context of this app can mean several things:

1. A Marlowe contract (a program that conforms to the schema defined in Marlowe.Semantics).
2. An instance of a Marlowe contract installed on the blockchain. These can be identified
   by their `MarloweParams`.
3. A Plutus contract. Marlowe Run uses three Plutus contracts to operated (see below).
4. An instance of a Plutus contract running in the PAB. These are identified by a
   `ContractInstanceId`.

## The Marlowe Plutus contracts

Marlowe Run needs three Plutus `ContractType`s to be available in the PAB:

1. `MarloweContract`: Every wallet has one instance of this contract installed in the PAB.
   This instance is used to:
   - "create" instances of a Marlowe contract (i.e. to install an instance of a Marlowe
     contract on the blockchain and distribute the role tokens)
   - "apply-inputs" to an instance of a Marlowe contract (i.e. perform an action to move
     that contract forward)
   - "redeem" payments made to a role token
   - "close" an instance of a Marlowe contract.
   Apart from "create", these endpoints all take `MarloweParams` as an argument, which
   identifies the instance of the Marlowe contract in question.
2. `WalletCompanionContract`: Every wallet has one instance of this contract installed in
   the PAB. It listens continuously for payments of role tokens to that wallet, and
   updates its observable state with an array of `(MarloweParams, MarloweData)`, one pair
   for each role token, hence one for each Marlowe contract for which this wallet has a
   role. We use this to determine when we need to create new `WalletFollowerContract`
   instances.
3. `WalletFollowerContract`: Every wallet has zero or more istances of this contract
   installed in the PAB. We use this to "follow" a Marlowe contract. Once a contract has
   been "created", and we have its `MarloweParams`, we use an instance of the
   `WalletFollowerContract` to track its history and status. Once we have called the
   "follow" endpoint of this contract (passing it the `MarloweParams`), its observable
   state will tell us everything we need to know about the contract, and will be updated
   when it changes.
