.. highlight:: haskell
.. _english_auction_tutorial:

English auction example
==========================

Overview
------------

.. note::
    The heart of the task here is to learn how to build a script that is smart enough to say yes or no regarding whether a transaction can consume an output in a way that matches the intended behavior. 

This tutorial describes the general structure, logic and code needed for designing and writing a Plutus smart contract that can be used for an English auction that is executed on the Cardano blockchain. 

Key aspects of this example are the EUTXO model, the concepts involved in designing the UTXOs and EUTXOs, Plutus code examples, and the actions required of the parties involved with the auction transactions. 

Specific code examples are included with detailed explanations of what the code is doing. 

General requirements or recommendations for the developer environment
------------------------------------------------------------------------

*For this section, include any general information, recommendations or tips to help developers have a smooth experience.*

*I don't know if these statements below are helpful or accurate. They come from the original version of this tutorial...*

The easiest way to build Plutus currently is to use Nix. The Plutus team is working on providing a Docker image, which will help.

Plutus is built with Haskell, which can have a tough learning curve for those coming from an imperative programming background.

Plutus is new and this means that there are not necessarily as many help resources available as we would prefer. However, some of the most helpful resources to know about are: 

* [A few links to helpful info/resources]
* StackOverflow posts?
* IOG Technical Community on Discord?
* Links to other IOG pages/resources?

Key concepts
----------------

EUTXO model 
~~~~~~~~~~~~~~~

In order to write Plutus smart contracts, you need to understand the accounting model that Plutus and Cardano use, which is the Extended Unspent Transaction Output (EUTXO) model. This is different than the Bitcoin and Ethereum models for creating smart contracts in some critical ways. Cardano's EUTXO model has some significant advantages, but it requires a new way of thinking about smart contracts. 

For a full description of the EUTXO model, please see: `The EUTXO Handbook <https://www.essentialcardano.io/article/the-eutxo-handbook>`_. 

Highlights of the EUTXO model -- maybe delete this section as unnecessary and out of scope 
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

UTXO, or unspent transaction outputs, are transaction outputs from previous transactions that have occurred on the blockchain and that have not yet been spent. The EUTXO model adds arbitrary logic capabilities to the transactions. 

Unlike the UTXO model, which has just one condition -- that the appropriate signature is present in the transaction -- we replace this with arbitrary logic. 

Instead of just having an address that corresponds to a public key that can be verified by a signature that is added to the transaction, we have more general addresses, not based on public keys or the hashes of public keys, but instead contain arbitrary logic which decides under which conditions a particular UTXO can be spent by a particular transaction. 

* Redeemer
* Script Context
* Bitcoin approach
* Ethereum approach
* Cardano approach

Diagram/graphic of how the smart contract works
--------------------------------------------------

*Need to reassess what sort of diagrams would be most helpful.*

The general flow of the English auction smart contract logic
----------------------------------------------------------------

Laying the groundwork
~~~~~~~~~~~~~~~~~~~~~~~~~

.. note::
    A transaction is something that contains an arbitrary number of inputs and an arbitrary number of outputs. The effect of a transaction is to consume inputs and produce new outputs.

In this English Auction example, the item owner, Alice, wants to auction an NFT (Non-fungible token), a native token on Cardano that exists only once. An NFT can represent a piece of digital art or possibly a real-world asset.

The auction takes into account these parameters: 

* the owner of the token, 
* the token itself, 
* a minimal bid, and 
* a deadline.

The owner creates a UTXO at the script output. 

The value of the UTXO is the NFT, and the datum initially is nothing. Later it will be the highest bidder and the highest bid. But at this stage, a bid has not yet taken place. 

On the blockchain you can’t have a UTXO that contains only native tokens. A UTXO always has to be accompanied by some Ada, but for the sake of simplicity we will temporarily ignore that requirement for now.

Bidder transactions
~~~~~~~~~~~~~~~~~~~~~~

In this example, Bob wants to bid 100 Ada for Alice's NFT. In order to do this, Bob creates a transaction with two inputs and one output. 

The two inputs are: 

* the auction UTXO 
* Bob's bid of 100 Ada 

The output is at the output script, but now the value and the datum have changed. Previously the datum was nothing but now it has the value of: (Bob, 100).

The value has changed. Now there is not only the NFT in the UTXO, but also the 100 Ada bid.

Redeemer
~~~~~~~~~~~

As a redeemer, in order to unlock the original auction UTXO, we use something called `Bid`. This is an algebraic data type. There will be other values as well. 

The auction script will check that all the conditions are satisfied. In this example, the script has to check these three conditions: 

1. The bid happens before the deadline. 
2. The bid is high enough. 
3. The correct inputs and outputs are present (meaning that the auction is an output containing the NFT and it has the correct datum). 

A second bidder
~~~~~~~~~~~~~~~~~~~~

Next, a second bidder, Charlie, wants to outbid Bob. Charlie wants to bid 200 Ada.

Charlie will create another transaction, this time one with two inputs and two outputs. 
The two inputs are: 

* the bid (Charlie's bid of 200 Ada)
* the auction UTXO

The two outputs are: 

* the updated auction UTXO 
* a UTXO that returns Bob's bid of 100 Ada 

.. note:: 
    To clarify, technically, the auction UTXO is not getting updated because nothing ever changes. Instead, 
    what really happens is that the old auction UTXO is spent and a new one is created. In a way this may feel like the auction UTXO is getting updated, but that isn't truly accurate. 

Bid redeemer logic
~~~~~~~~~~~~~~~~~~~~~

This time we again use the `Bid` redeemer. The script has to check that these conditions are satisfied: 

* The deadline has been reached. 
* The bid is higher than the previous bid. 
* The auction UTXO is correctly created. 
* The previous highest bidder gets their bid back. 

Transactions for closing the auction
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Finally, for this example, let’s assume that there won’t be another bid. Once the deadline has passed, the auction can be closed. 

In order to do that, somebody has to create another transaction. That could be Alice who wants to collect the bid or it could be Charlie who wants to collect the NFT. It can be anybody, but Alice and Charlie have an incentive to create it. 

This transaction will have one input: 

* the auction UTXO, this time with the `Close` redeemer. 

This transaction will have two outputs: 

* One output is for the highest bidder, Charlie, who gets the NFT. 
* The second output goes to Alice who gets the highest bid.

Logic
~~~~~~~~~~

In the Close case, the script checks that these conditions are satisfied: 

* The deadline has been reached. 
* The winner gets the NFT. 
* The auction owner gets the highest bid. 

When there are no bidders
~~~~~~~~~~~~~~~~~~~~~~~~~~~

Finally, we need to consider the scenario in which nobody bids in the auction. Alice creates the auction, but the auction receives no bids. In this case, there must be a mechanism for Alice to retrieve her NFT.

To address this possibility, Alice creates a transaction with the `Close` redeemer. However, because there is no bidder, the NFT doesn’t go to the highest bidder, but instead simply goes back to Alice. 

The logic in this case is slightly different. It will check that the NFT goes back to Alice. However, it doesn’t need to check the recipient because the transaction will be triggered by Alice and she can send the NFT wherever she wants. 

On-chain code explanation
-----------------------------

On-chain code is the scripts we were discussing -- the scripts from the EUTXO model. In addition to public key addresses, we have a script address. Outputs can sit at such an address, and if a transaction tries to consume such an output, the script is executed. The transaction is only valid if the script succeeds.

If a node receives a new transaction, it validates it before accepting it into its mempool and eventually into a block. For each input of the transaction, if that input happens to be a script address, the corresponding script is executed. If the script does not succeed, the transaction is invalid.

Plutus Core
~~~~~~~~~~~~~~

The programming language this script is expressed in is called Plutus Core, but you never write Plutus Core by hand. Instead, you write Haskell and that gets compiled down to Plutus Core. Eventually there may be other high-level languages such as Solidity, C or Python that can compile down to Plutus Core.

The task of a script is to say yes or no regarding whether a transaction can consume an output.

Example code
~~~~~~~~~~~~~~~~

Code sample::

    {-# INLINABLE mkAuctionValidator #-}
    mkAuctionValidator :: AuctionDatum -> AuctionAction -> ScriptContext -> Bool
    mkAuctionValidator ad redeemer ctx =
        traceIfFalse "wrong input value" correctInputValue &&
        case redeemer of
            MkBid b@Bid{..} ->
                traceIfFalse "bid too low" (sufficientBid bBid)                &&
                traceIfFalse "wrong output datum" (correctBidOutputDatum b)    &&
                traceIfFalse "wrong output value" (correctBidOutputValue bBid) &&
                traceIfFalse "wrong refund"       correctBidRefund             &&
                traceIfFalse "too late"           correctBidSlotRange
            Close           ->
                traceIfFalse "too early" correctCloseSlotRange &&
                case adHighestBid ad of
                    Nothing      ->
                        traceIfFalse "expected seller to get token" (getsValue (aSeller auction) tokenValue)
                    Just Bid{..} ->
                        traceIfFalse "expected highest bidder to get token" (getsValue bBidder tokenValue) &&
                        traceIfFalse "expected seller to get highest bid" (getsValue (aSeller auction) $ Ada.lovelaceValueOf bBid)

    where
        info :: TxInfo
        info = scriptContextTxInfo ctx

        input :: TxInInfo
        input =
        let
            isScriptInput i = case (txOutDatumHash . txInInfoResolved) i of
                Nothing -> False
                Just _  -> True
            xs = [i | i <- txInfoInputs info, isScriptInput i]
        in
            case xs of
                [i] -> i
                _   -> traceError "expected exactly one script input"

        inVal :: Value
        inVal = txOutValue . txInInfoResolved $ input

        auction :: Auction
        auction = adAuction ad

        tokenValue :: Value
        tokenValue = Value.singleton (aCurrency auction) (aToken auction) 1

        correctInputValue :: Bool
        correctInputValue = inVal == case adHighestBid ad of
            Nothing      -> tokenValue
            Just Bid{..} -> tokenValue Plutus.<> Ada.lovelaceValueOf bBid

        sufficientBid :: Integer -> Bool
        sufficientBid amount = amount >= minBid ad

        ownOutput   :: TxOut
        outputDatum :: AuctionDatum
        (ownOutput, outputDatum) = case getContinuingOutputs ctx of
            [o] -> case txOutDatumHash o of
                Nothing   -> traceError "wrong output type"
                Just h -> case findDatum h info of
                    Nothing        -> traceError "datum not found"
                    Just (Datum d) ->  case PlutusTx.fromData d of
                        Just ad' -> (o, ad')
                        Nothing  -> traceError "error decoding data"
            _   -> traceError "expected exactly one continuing output"

        correctBidOutputDatum :: Bid -> Bool
        correctBidOutputDatum b = (adAuction outputDatum == auction)   &&
                                (adHighestBid outputDatum == Just b)

        correctBidOutputValue :: Integer -> Bool
        correctBidOutputValue amount =
            txOutValue ownOutput == tokenValue Plutus.<> Ada.lovelaceValueOf amount

        correctBidRefund :: Bool
        correctBidRefund = case adHighestBid ad of
            Nothing      -> True
            Just Bid{..} ->
            let
                os = [ o
                    | o <- txInfoOutputs info
                    , txOutAddress o == pubKeyHashAddress bBidder
                    ]
            in
                case os of
                    [o] -> txOutValue o == Ada.lovelaceValueOf bBid
                    _   -> traceError "expected exactly one refund output"

        correctBidSlotRange :: Bool
        correctBidSlotRange = to (aDeadline auction) `contains` txInfoValidRange info

        correctCloseSlotRange :: Bool
        correctCloseSlotRange = from (aDeadline auction) `contains` txInfoValidRange info

        getsValue :: PubKeyHash -> Value -> Bool
        getsValue h v =
        let
            [o] = [ o'
                | o' <- txInfoOutputs info
                , txOutValue o' == v
                ]
        in
            txOutAddress o == pubKeyHashAddress h


Brief description of what the off-chain code does
----------------------------------------------------


