# The Extended UTxO Model
#plutus/extended-utxo

The *extended UTxO model* brings a significant portion of the expressiveness of Ethereum’s account-based scripting model to the UTxO-based Cardano blockchain. The extension has two components: (1) an extension to the data carried by UTxO outputs and processed by associated validator scripts together with (2) an extension to the wallet backend to facilitate off-chain code that coordinates the execution of on-chain computations.

## Extension to transaction outputs
In the classic UTxO model (Cardano SL in Byron and Shelley), a transaction output locked by a script carries two pieces of information:

1. its value and
2. (the hash of) a validator script.

We extend this to include a second script, which we call the *data script*. This second script is a Plutus Core expression, just like the validator script. However, the requirements on its type are different. The type of the data script can be any monomorphic type.

## Extension to transactions (deterministic scripts)
All transactions carry a validity interval (an interval of slots) as additional data. Core nodes do not attempt to validate transactions if the current slot is outside of this interval. When a scripted transaction input is validated, the validity interval is passed to the validator script, as a way of providing information about the current time. This makes script validation completely deterministic in the sense that all arguments to the validator script are known before the transaction is submitted to the chain. As a result, the exact amount of gas that is required to run the script can be calculated in advance (by running it), and users do not risk being surprised by failed validations that still incur fees.

## Extension to validator scripts
An extended validator script expects four arguments:

1. the redeemer expression,
2. the data script (from above),
3. the output’s value, and
4. parts of the validated transaction and related blockchain state. (More detail is in the next section.)

We consider a validator script to have executed successful if it does not terminate in the Plutus Core `error` state.

## Blockchain state available to validator scripts
Validator scripts receive, at a minimum, the following information from the validated transaction and the rest of the blockchain:

1. the validity interval of the currently validated transaction
2. the hash of the currently validated transaction,
3. for every input of the validated transaction, its value and the hashes of its validator, data, and redeemer scripts,
4. for every output of the validated transaction, its value and the hash of its validator and data script, and
5. the sum of the values of all unspent outputs (of the current blockchain without the currently validated transaction) locked by the currently executed validator script.

We may want to support the validator being able to query the sum of all values of all unspent outputs locked by other script addresses, too. This may be costly, though.

## Scripts and signatures

For each of the three script types (data, validator, redeemer) there are two artifacts on the blockchain: The script itself, and its hash. Each artifact can be provided either as part of the producing transaction's output, or as part of the consuming transaction's input. We can organise the three types by according to who provides the script, and who provides the hash, resulting in the following matrix.

|| Signed by Producer | Signed by Consumer |
|-|-|-|
|**Provided by Producer**| Data script | *N/A\** |
|**Provided by Consumer**| Validator script | Redeemer script |

The validator script must be submitted as part of the consuming transaction's input, but its content is determined by the producing transaction. Both the hash and content of the data script are provided by the producing transaction, and the hash and content of the redeemer are provided by the consumer. 

When a transaction is validated, the validator script receives data and redeemer scripts and either terminates successfully or in the Plutus `error` state. This means that the producing transaction effectively determines the type of the redeemer script, even though the script itself (ie. a value of that type) is not known at that time. (One has to be careful not to lock a transaction output permanently by specifying a type that has no values other than `error`)

**(*)** It is possible that the top right quadrant (provided by producer, signed by consumer) can be filled with a meaningful fourth type of script, perhaps to enable interactions with third parties. 

## Script support for UTxO wallets
Off-chain script coordination code necessarily needs to execute in the context of a wallet. At a minimum, off-chain code needs to be able to submit transactions, which need to include transaction fees, which in turn need to be covered from the funds of a wallet. Moreover, transaction submission is dependent on wallet functionality like coin selection.

### Script UTxO
The [wallet specification](https://cardanodocs.com/files/formal-specification-of-the-cardano-wallet.pdf) is based on a notion of owned addresses, as determined by the `ours` predicate. These are the addresses for which UTxO sets are computed by the wallet.

Scripts are interested in additional addresses and a wallet with scripts needs to maintain an additional UTxO set, which we call the *script UTxO*. The set of addresses tracked by the script UTxO is explicitly nominated by the scripts included in the wallet. This is not unlike the process of subscribing to the events generated by a socket in POSIX.

Consequences of that extension are the following.

On Page 9 of the wallet spec, the precondition for `newPending` needs to be adapted to the fact that a new pending transaction can now contain inputs that spend outputs whose (script) address the wallet does not own, but that are locked by a script for which the wallet can create a valid redeemer script. *We handle this by doing the same with the script UTxO as we are doing with the wallet address UTxO, but just for the script inputs.* This ensures locally that we only create transactions that refer to existing unspent outputs and are not double spending.

* This also affects the removal of transactions from the pending set (if one of their script inputs is spent, they also need to be removed).

* It also affects prefiltering, as we are interested in a range of script addresses in addition to the addresses we own.

### Rollbacks
#plutus/extended-utxo/rollbacks

Given that blockchain events, such as the confirmation of a transaction, can trigger the execution of off-chain coordination code, we need to carefully consider the implications of needing to rollback any action that depends on a rolled back transaction.

In order to avoid rollbacks, we would need to wait for 2160 blocks (the security parameter k in the specification) before acting on a confirmation (with 20s per block, it would be a 12 hour delay). However, we can distinguish different kinds of actions that might be triggered by events and many of them don’t need that level of assurance. Generally, we distinguish between three kinds of actions that can occur in response to an event: 

1. the creation of dependent transactions, 
2. the creation of independent transactions, and 
3. general effects.

In the first case, there is no need to wait, and we can immediately react to an event. As the newly created transaction is dependent on the transaction that triggered the event, the newly created transaction will also be rolled back if the event-trigger is rolled back. In the other two cases, we need to be more careful and the most appropriate behaviour will depend on the risks involved. In general, we will need to wait for an application-specific block depth before processing the event. It probably makes sense to let the script specify that delay when it registers an address for observation.

Ideally, we would want to distinguish the case of the creation of a dependent transaction from the other cases by way of the type system to avoid the accidental immediate reaction in anything, but the first of the three cases.

### Total balance
Just like in Section 7 of the wallet spec (for rollbacks), the notion of a total balance makes no sense in the presence of pending *script* transactions. Just like expected transactions, script transactions can spend from outputs that do not belong to us (in the sense of the wallet).

I think, it would be reasonable, for the change computation, to simply disregard pending transactions where one or more inputs spend script addresses.

### Time-To-Live (TTL)
TTL support (Section 10.4 of the specification) appears rather desirable in the presence of scripts as script codes will generally want to work with timeouts given the highly asynchronous nature of transaction propagation and confirmation in a blockchain.

## Wallet API for scripts

Plutus Core (PLC) scripts end up on the blockchain as part of transactions, which are created by wallets. The Plutus coordinating code interacts with a wallet through the wallet API. This API needs to be extended to support:

1. Creating transactions based on *transaction templates* 
2. Registering to be notified on events related to the state of the blockchain (consider [Rollbacks](#plutus/extended-utxo/rollbacks) as well)
3. (Potentially) Performing operations that require a private key, such as signing the redeemer script. Plutus coordinating code should not have to handle private keys.

Transaction templates differ from normal transactions in two ways:

1. Some of their output value is not matched by transaction inputs. The wallet is expected to add the missing inputs (coin selection)
2. They do not include transaction fees. The wallet is expected to compute the fees and either add them to the inputs, or subtract them to the outputs if possible. The exact behaviour should be configurable by the user. (Note that changing the inputs and outputs affects the transaction fees)
