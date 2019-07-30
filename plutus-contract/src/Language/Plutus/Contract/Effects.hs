{-# LANGUAGE ConstraintKinds  #-}
{-# LANGUAGE DataKinds        #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeOperators    #-}
module Language.Plutus.Contract.Effects(
    module X
    , ContractActions
    , ContractEffects
    , runEffects
    ) where

import           Control.Eff
import           Control.Eff.Exception
import           Control.Eff.Reader.Lazy

import           Language.Plutus.Contract.Effects.AwaitSlot      as X
import           Language.Plutus.Contract.Effects.ExposeEndpoint as X
import           Language.Plutus.Contract.Effects.WatchAddress   as X
import           Language.Plutus.Contract.Effects.WriteTx        as X

import           Language.Plutus.Contract.Prompt.Event           (Event)
import           Language.Plutus.Contract.Prompt.Hooks           (Hook)

{- Note [Contract Effects]

We model effects of Plutus contracts using 'Control.Eff'. The ones
exported here are the basic effects that we need for our use cases (wait for a
slot, expose an endpoint, watch an address on the blockchain, and submit
transactions). To make these easier to use we export them as the
'ContractActions' constraint.

To our users, the signatures of our contracts look like '(ContractActions r) =>
Contract r ()'.

Internally, all effects are interpreted as request-response pairs. The four
effects 'AwaitSlot', 'ExposeEndpoint', 'WatchAddress' and 'WriteTx' have a
common type for requests ('Hook') and a common type for responses ('Event').

'runEffects' takes the user-facing contract request types and interprets them
in '[Reader (Maybe Event), Exc (Hook ())]]' -- effectively 'Maybe Event -> Either (Hook ()) a'.

-}

-- | Basic interactions with the app platform (write transactions, wait for
--   slot changes, watch addresses, expose endpoints).
type ContractActions r = [WriteTx, AwaitSlot, WatchAddress, ExposeEndpoint] <:: r

-- | List of effects that this interpreter ('Maybe Event -> Either Hooks a')
--   supports.
type ContractEffects r =
    WriteTx ': AwaitSlot ': WatchAddress ': ExposeEndpoint ': PromptEffects r

type PromptEffects r = Reader (Maybe Event) ': Exc (Hook ()) ': Exc String ': r

-- | Interpret the 'PlutusEffects' in 'Reader' and 'Exc'. See note [Contract
--   Effects]
runEffects :: Eff (ContractEffects r) a -> Eff (PromptEffects r) a
runEffects =
        runExposeEndpoint
        . runWatchAddress
        . runAwaitSlot
        . runWriteTx

{- Note [Hooks and Events]

The three types 'Hook', 'Hooks' and 'Event' are closely related.

* `Hook a` values are produced by the smart contract. They describe events that
  the contract is waiting for. For example, `AddrHook :: Address -> Hook a`
  means "I want to know the next transaction that affects this address". The
  type parameter `a` is currently always the unit type, so it is effectively
  unused. This parameter will hold information about the type (schema) of
  endpoints that the contract exposes.

* `Hooks` is a set of all hooks that the contract exposes in its current state.
  The contract may have multiple branches running in parallel, and when a branch
  gets blocked on a `Hook ()`, that hook is included in the `Hooks` value that
  is returned to the client.

* `Event` values are produced by the app platform. Each constructor of `Event`
  corresponds to a constructor of `Hook a`. For example, `LedgerUpdate ::
  Address -> Tx -> Event` is the counterpart of `AddrHook`.

To the outside world, the contract is essentially a state machine `Record -> Event -> (Hooks, Record)` where `Record` is an opaque blob that the caller
needs to store after each call. The `Event` should correspond to one of the `Hooks` of the previous call.

TODO: Use the type parameter of `Hooks` to encode the type of endpoints that a
   contract may expose. Once we can do that, we can generalise the notion of
    endpoints to mean any kind of capability that the contract may need (submit
    transactions, sign things, make HTTP calls, etc), not just user-facing
    endpoints. Then we can get rid of all other constructors in `Hook` and
    `Event`.

TODO: Directly match `Event`s to `Hook`s, using request IDs. This will make
   the contract code slightly more efficient since we won't have to try the same
   event in multiple branches anymore, and it would be especially useful for the
   `SubmitTransaction` hook because we currently can't refer to the transaction
   after submitting it.

-}
