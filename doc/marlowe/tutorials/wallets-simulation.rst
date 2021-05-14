.. _wallets-simulation:

Wallets Simulation
==================

The wallets simulation is a "bleeding-edge" feature that is still under
development however it’s already an interesting way to understand how a
Marlowe contract will function in more detail and how a contract will
appear from the perspective of each party involved.

If you click on the fifth tab in the playground, labelled "Wallets", you
will be presented with an almost blank screen with just a few possible
actions. This pane will soon show various wallets involved in a contract
however first you need to create those wallets. Click on the ``+``
button to create a new wallet.

Wallet Contents
---------------

A wallet contains the following:

-  Assets - these are tokens that the wallet owns, such as some Ada.

-  Roles - these are contract roles that a wallet owns. If you own a
   role then you can take contract actions on behalf of those roles.

-  Contracts - a wallet can be involved in mutliple running contracts.

To get started we need a valid contract, so go back to the "Simulation"
tab and load the example "Escrow" contract. Now go back to the "Wallets"
tab and click on "Load Contract from Simulation". This will load the
contents of the Simulation editor as long as it is currently valid (in
our case, the Escrow contract). You will see the contents of the
contract as well as any roles that appear (in our case alice, bob and
carol).

Roles
-----

The roles are owned by the wallet that loaded the contract at the start
but we can transfer them to other wallets. Click on the ``+`` button
again to create a new wallet. This wallet will now be empty but lets go
back to "Wallet 1" and transfer ownership of the role "alice" to "Wallet
2" by selecting it from the drop-down list.

Now go back to "Wallet 2" and you will see that the role "alice" has
been transfered to "Wallet 2" as well as "Contract 1" being displayed.
The contract is displayed because Wallet 2 is now involved in the
contract (since it owns the role alice).

Running a contract
------------------

Stay in Wallet 2 and lets start the contract by clicking on the "Start"
button. You will now see the current state of the contract displayed as
well as possible actions. In our case it is possible to make a deposit
on behalf of alice.

Let’s go back to Wallet 1 and you will see that there are no possible
actions, this is because the escrow contract can only progress if alice
makes a deposit (or if the contract expires).

Taking Actions
--------------

Let’s go back to Wallet 2 and add the deposit input to the transaction
composer by clicking on the ``+`` button. You should see an error
message ``Insufficient funds to add this input``. The wallet needs to
deposit 450 lovelace but it doesn’t have any! Go to the top of the page
and add 1000 lovelace using the input box and click the ``+`` button.
You should now see under assets that Wallet 2 has 1000 lovelace. Now we
can add the input to the transaction compser again.

You should see that the Deposit has moved to the transaction composer
and a new input is available. It is possible to make a multiple inputs
in a single transaction but for now we will just add one. Click the
"Apply" button and you should see that both the state and the contract
have changed. You will also notice under Assets that Wallet 2 now only
has 550 lovelace.

At this point, alice is still the only role that can progress the
contract so let’s go ahead and create a new transaction with the input
of alice choosing 0. Once we apply this transaction we will see that
there are now no longer any further possible actions we can take. Go
back to Wallet 1 and we can see that there is now a possible input that
we can take. Lets construct a transaction of Bob choosing 0 and click
"Apply".

The state changes again and the contract is now closed, no further
actions can be taken. We can also see that the 450 have been transfered
to Wallet 1. This is because Wallet 1 owns the role bob and the contract
stated that if both alice and bob chose 0 then the 450 lovelace should
be transfered to bob.

Other Features
--------------

It is possible to have multiple contracts running at the same time. You
can go back to the Simulation tab and create a different contract then
go to the Wallets tab and "Load Contract from Simulation" again.

You can move to the Next slot in the block chain by pressing the "Next
Slot" link on the right-hand side.

The state of the blockchain can be reset by clicking on the "Reset
Blockchain" link, also on the right-hand side. This will "go backwards
in time" and undo all actions taken as well as resetting the slot number
to 0.

Finally you can reset the whole simulation by clicking on the "Clear
All" link at the top. This will delete all wallets and loaded contracts
and reset the blockchain to slot 0.

Final Notes
-----------

As stated at the beginning of this section, the Wallets simulation is a
new feature and we intend to develop it further in the future however
hopefully it has given you a better understanding of how a contract will
develop in the real world and how it will appear to real users.
