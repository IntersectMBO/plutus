-- editorconfig-checker-disable-file
{-# LANGUAGE DataKinds         #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell   #-}

module AuctionValidator where

import PlutusCore.Default qualified as PLC
import PlutusLedgerApi.V1 (POSIXTime, PubKeyHash, Value, adaSymbol, adaToken, singleton)
import PlutusLedgerApi.V1.Address (pubKeyHashAddress)
import PlutusLedgerApi.V1.Interval (contains)
import PlutusLedgerApi.V2 (Datum (..), OutputDatum (..), ScriptContext (..), TxInfo (..), TxOut (..), from, to)
import PlutusLedgerApi.V2.Contexts (getContinuingOutputs)
import PlutusTx
import PlutusTx.Bool
import PlutusTx.Builtins
import PlutusTx.Lift
import PlutusTx.Maybe
import PlutusTx.Prelude qualified as PlutusTx
import PlutusTx.Show qualified as PlutusTx
import Prelude qualified as Haskell

-- BLOCK1
data AuctionParams = AuctionParams
  { apSeller  :: PubKeyHash,
    apAsset   :: Value,
    apMinBid  :: Integer,
    apEndTime :: POSIXTime
  }

PlutusTx.makeLift ''AuctionParams

data Bid = Bid
  { bBidder :: PubKeyHash,
    bAmount :: Integer
  }

PlutusTx.deriveShow ''Bid
PlutusTx.unstableMakeIsData ''Bid

instance PlutusTx.Eq Bid where
  {-# INLINEABLE (==) #-}
  bid == bid' =
    bBidder bid PlutusTx.== bBidder bid'
      PlutusTx.&& bAmount bid PlutusTx.== bAmount bid'

newtype AuctionDatum = AuctionDatum { adHighestBid :: Maybe Bid }

PlutusTx.unstableMakeIsData ''AuctionDatum

data AuctionRedeemer = NewBid Bid | Payout

PlutusTx.unstableMakeIsData ''AuctionRedeemer
-- BLOCK2


{-# INLINEABLE auctionTypedValidator #-}
auctionTypedValidator ::
  AuctionParams ->
  AuctionDatum ->
  AuctionRedeemer ->
  ScriptContext ->
  Bool
auctionTypedValidator params (AuctionDatum highestBid) redeemer ctx@(ScriptContext txInfo _) =
  PlutusTx.and conditions
  where
    conditions :: [Bool]
    conditions = case redeemer of
      NewBid bid ->
        [ -- The new bid must be higher than the highest bid.
          -- If this is the first bid, it must be at least as high as the minimum bid.
          sufficientBid bid,
          -- The bid is not too late.
          validBidTime,
          -- The previous highest bid should be refunded.
          refundsPreviousHighestBid,
          -- A correct new datum is produced, containing the new highest bid.
          correctNewDatum bid
        ]
      Payout ->
        [ -- The payout is not too early.
          validPayoutTime,
          -- The seller gets the highest bid.
          sellerGetsHighestBid,
          -- The highest bidder gets the asset.
          highestBidderGetsAsset
        ]
-- BLOCK3
    sufficientBid :: Bid -> Bool
    sufficientBid (Bid _ amt) =
      maybe
        (amt PlutusTx.>= apMinBid params)
        (\(Bid _ amt') -> amt PlutusTx.> amt')
        highestBid
-- BLOCK4
    validBidTime :: Bool
    validBidTime = to (apEndTime params) `contains` txInfoValidRange txInfo
-- BLOCK5
    refundsPreviousHighestBid :: Bool
    refundsPreviousHighestBid = case highestBid of
      Nothing -> True
      Just (Bid bidder amt) ->
        case PlutusTx.filter
          (\o -> txOutAddress o PlutusTx.== pubKeyHashAddress bidder)
          (txInfoOutputs txInfo) of
          [o] -> txOutValue o PlutusTx.== singleton adaSymbol adaToken amt
          os ->
            PlutusTx.traceError
              ( "Expected exactly one refund output, got "
                  PlutusTx.<> PlutusTx.show (PlutusTx.length os)
              )
-- BLOCK6
    correctNewDatum :: Bid -> Bool
    correctNewDatum bid = case getContinuingOutputs ctx of
      [o] -> case txOutDatum o of
        OutputDatum (Datum newDatum) -> case PlutusTx.fromBuiltinData newDatum of
          Just bid' ->
            PlutusTx.traceIfFalse
              ( "Invalid output datum: expected "
                  PlutusTx.<> PlutusTx.show bid
                  PlutusTx.<> ", but got "
                  PlutusTx.<> PlutusTx.show bid'
              )
              (bid PlutusTx.== bid')
          Nothing ->
            PlutusTx.traceError
              ( "Failed to decode output datum: "
                  PlutusTx.<> PlutusTx.show newDatum
              )
        OutputDatumHash _ ->
          PlutusTx.traceError "Expected OutputDatum, got OutputDatumHash"
        NoOutputDatum ->
          PlutusTx.traceError "Expected OutputDatum, got NoOutputDatum"
      os ->
        PlutusTx.traceError
          ( "Expected exactly one continuing output, got "
              PlutusTx.<> PlutusTx.show (PlutusTx.length os)
          )
-- BLOCK7
    validPayoutTime :: Bool
    validPayoutTime = from (apEndTime params) `contains` txInfoValidRange txInfo

    sellerGetsHighestBid :: Bool
    sellerGetsHighestBid = case highestBid of
      Nothing -> True
      Just (Bid _ amt) ->
        case PlutusTx.filter
          ( \o ->
              txOutAddress o PlutusTx.== pubKeyHashAddress (apSeller params)
                PlutusTx.&& txOutValue o PlutusTx.== singleton adaSymbol adaToken amt
          )
          (txInfoOutputs txInfo) of
          [_] -> True
          os ->
            PlutusTx.traceError
              ( "Expected exactly one output paid to the seller, got "
                  PlutusTx.<> PlutusTx.show (PlutusTx.length os)
              )

    highestBidderGetsAsset :: Bool
    highestBidderGetsAsset = case highestBid of
      Nothing -> True
      Just (Bid bidder _) ->
        case PlutusTx.filter
          ( \o ->
              txOutAddress o PlutusTx.== pubKeyHashAddress bidder
                PlutusTx.&& txOutValue o PlutusTx.== apAsset params
          )
          (txInfoOutputs txInfo) of
          [_] -> True
          os ->
            PlutusTx.traceError
              ( "Expected exactly one output paid to the highest bidder, got "
                  PlutusTx.<> PlutusTx.show (PlutusTx.length os)
              )
-- BLOCK8
{-# INLINEABLE auctionUntypedValidator #-}
auctionUntypedValidator :: AuctionParams -> BuiltinData -> BuiltinData -> BuiltinData -> ()
auctionUntypedValidator params datum redeemer ctx =
  PlutusTx.check
    ( auctionTypedValidator
        params
        (PlutusTx.unsafeFromBuiltinData datum)
        (PlutusTx.unsafeFromBuiltinData redeemer)
        (PlutusTx.unsafeFromBuiltinData ctx)
    )

auctionValidatorScript ::
  AuctionParams ->
  CompiledCode (BuiltinData -> BuiltinData -> BuiltinData -> ())
auctionValidatorScript params =
  $$(PlutusTx.compile [||auctionUntypedValidator||])
    `PlutusTx.applyCode` PlutusTx.liftCode params
-- BLOCK9
