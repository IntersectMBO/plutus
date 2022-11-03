.. highlight:: haskell
.. _english_auction_tutorial:

English Auction Example
==========================

Overview
------------

General requirements of the developer environment
------------------------------------------------------

How the Plutus Tx on-chain code works
------------------------------------------

Key concepts overview
------------------------

EUTXO model 
~~~~~~~~~~~~~~~

Ledger
~~~~~~~~~~

Diagram/graphic of how the smart contract works
--------------------------------------------------

Code explanation
---------------------

Example code
~~~~~~~~~~~~~~~~

Brief description of what the off-chain code does
----------------------------------------------------

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



