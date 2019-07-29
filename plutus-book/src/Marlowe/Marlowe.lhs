[source,haskell]
----
{-# LANGUAGE DeriveAnyClass     #-}
{-# LANGUAGE DerivingStrategies #-}
module Marlowe.Marlowe where

import           GHC.Generics            (Generic)
-- Marlowe has its own pretty printer
import           Marlowe.Language.Marlowe.Pretty as Pretty

prettyPrint :: Contract -> String
prettyPrint = show . Pretty.pretty

-- Integer type wrappers used in building a Contract

type BlockNumber = Integer
type Timeout = BlockNumber
type Person = Integer
type Choice = Integer


-- Integer wrappers for unique identifiers to refer to specific Contract terms within a Contract definition

type IdAction = Integer
type IdCommit = Integer
type IdChoice = (Integer, Person)
type IdOracle = Integer

type LetLabel = Integer
----

The `Value` datatype represents an `Integer` value, and is used in place of
`Integer` in a `Contract`. It additionally contains all the constructors
that will be interpreted as the integer functions and calculations permissible
in a contract.

[source,haskell]
----
data Value = CurrentBlock |
             Committed IdCommit |
             Constant Integer |
             NegValue Value |
             AddValue Value Value |
             SubValue Value Value |
             MulValue Value Value |
             DivValue Value Value Value |
 --          dividend-^ divisor-^ ^-default value (in case divisor is zero)
             ModValue Value Value Value |
 --          dividend-^ divisor-^ ^-default value (in case divisor is zero)
             ValueFromChoice IdChoice Value |
 --    default value if not available --^
             ValueFromOracle IdOracle Value
 --    default value if not available --^
               deriving stock (Eq, Ord, Show, Generic, Read)
               deriving anyclass (Pretty.Pretty)

----

Terms of type `Observation` represent a specialized subset of predicates which are used
defining a `Contract`. They will be interpreted as standard predicates.

[source,haskell]
----

data Observation = BelowTimeout Timeout |            -- the current time is before a given timeout
                   AndObs Observation Observation |  -- and
                   OrObs Observation Observation |   -- or
                   NotObs Observation |              -- not
                   ChoseThis IdChoice Choice |       -- <1>
                   ChoseSomething IdChoice |         -- <2>
                   ValueGE Value Value |             -- greater than or equal to
                   ValueGT Value Value |             -- greater than
                   ValueLT Value Value |             -- less than
                   ValueLE Value Value |             -- less than or equal to
                   ValueEQ Value Value |             -- equal to
                   TrueObs |                         -- true
                   FalseObs                          -- false
               deriving stock (Eq, Ord, Show, Generic, Read)
               deriving anyclass (Pretty.Pretty)

----

<1> A participant made a choice (i.e. entered a _specific_ `Choice int` value), and this
choice action has an ID `IdChoice int`

<2> A participant made _some_ choice, and this
choice action has an ID `IdChoice int`

Note that in both cases the (integer) value that was chosen can be referred
to in the `ValueFromChoice` constructor of `Value` by the `IdChoice` identifier.
This is how an observation that a choice was made can be used as data in
in a `Contract`. For example, as we will see as well, a participant may decide
on the amount of money they commit to a contract.

Finally, we introduce the `Contract` structure itself. It is not possible to
define a non-terminating contract in this DSL. This is a very important feature
expected of smart contracts, and forcing the evaluation of all arguments
makes sense here.

[source,haskell]
----
data Contract =
    Null |                                                                            -- <1>
    Commit !IdAction !IdCommit !Person !Value !Timeout !Timeout !Contract !Contract | -- <2>
    Pay !IdAction !IdCommit !Person !Value !Timeout !Contract !Contract |             -- <3>
    Both !Contract !Contract |                                                        -- <4>
    Choice !Observation !Contract !Contract |                                         -- <5>
    When !Observation !Timeout !Contract !Contract |                                  -- <6>
    While !Observation !Timeout !Contract !Contract |                                 -- <7>
    Scale !Value !Value !Value !Contract |                                            -- <8>
    Let !LetLabel !Contract !Contract |                                               -- <9>
    Use !LetLabel                                                                     -- <10>
               deriving stock (Eq, Ord, Show, Generic, Read)
               deriving anyclass (Pretty.Pretty)
----

<1> `Null` is the trivial contract, where no participants can perform any actions
and there is no more program to execute. This contract is always fulfilled!

<2> `Commit idA idC p v t1 t2 c1 c2` constructor allows a participant to commit cash
to a contract, taking the following arguments

* `idA` - not needed for the intended functionality
* `idC` - unique identifier of this cash commit (can use it within this contract
to refer to the committed cash)
* `p`   - the ID of the person who is expected to commit the cash
* `v`   - the amount of cash to be committed
* `t1`  - the block (slot) number after which the commit can no longer be made,
and the contract evaluates to `c2`
* `t2`  - the block (slot) number after which the cash committed by `p` to this
contract will be returned to `p` at this time, and every other commit belonging to
the contract at that time will also be returned to the participant who made it
* `c1`  - the contract to which `Commit idA idC p v t1 t2 c1 c2` evaluates
when `p` makes the commit (of value `v` before time `t1`)
* `c2`  - the contract to which `Commit idA idC p v t1 t2 c1 c2` evaluates
when `p` does not make the correct cash commit before the timeout

<3> `Pay idA idC p v t1 c1 c2` constructor represents the contract paying
some of the funds locked in it to a participant, with the following arguments

* `idA` - not needed for the intended functionality
* `idC` - unique identifier of this payment action (can use it within this contract
to refer to this payment)
* `p`   - the ID of the person to who the contract pays
* `v`   - the amount of cash to be paid
* `t1`  - the block (slot) number after which the payment can no longer be made,
and the contract evaluates to `c2`
* `c1`  - the contract to which `Pay idA idC p v t1 c1 c2` evaluates
when a successful payment is made before the timeout `t1`
* `c2`  - the contract to which `Pay idA idC p v t1 c1 c2` evaluates
otherwise

<4> `Both c1 c2` constructor represents a contract that requires both
`c1` and `c2` to be fulfilled

<5> `Choice obs c1 c2` constructor represents the contract which is equivalent
to (evaluates to) `c1` when `obs` is true, and `c2` otherwise

<6> `When obs t c1 c2` constructor represents the contract that evaluates to
`c1` as soon as `obs` becomes true, provided it is at or before timeout `t`,
otherwise, it evaluates to `c2`

<7> `While obs t c1 c2` constructor represents the contract that evaluates to
`c1` while `obs` is true and until the timeout `t`, and to `c2` otherwise

We will not give the details of 8, 9 or 10 as they are no longer in use in the
most recent Marlowe version. We now go on to discuss interpreting the intended
functionality of the above data structures with the validator-redeemer-data
script model on the mockchain and in the mock wallet.
