{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE DerivingStrategies    #-}
{-# LANGUAGE ImportQualifiedPost   #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE PatternSynonyms       #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE Strict                #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE ViewPatterns          #-}

{-# OPTIONS_GHC -fno-ignore-interface-pragmas #-}
{-# OPTIONS_GHC -fno-omit-interface-pragmas #-}
{-# OPTIONS_GHC -fno-full-laziness #-}
{-# OPTIONS_GHC -fno-spec-constr #-}
{-# OPTIONS_GHC -fno-specialise #-}
{-# OPTIONS_GHC -fno-strictness #-}
{-# OPTIONS_GHC -fno-unbox-strict-fields #-}
{-# OPTIONS_GHC -fno-unbox-small-strict-fields #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:target-version=1.0.0 #-}

module AuctionValidator where

import PlutusCore.Version (plcVersion100)
import PlutusLedgerApi.V1 (Lovelace, POSIXTime, PubKeyHash, Value)
import PlutusLedgerApi.V1.Address (pubKeyHashAddress)
import PlutusLedgerApi.V1.Interval (contains)
import PlutusLedgerApi.V1.Value (lovelaceValue)
import PlutusLedgerApi.V2 (Datum (..), OutputDatum (..), ScriptContext (..), TxInfo (..),
                           TxOut (..), from, to)
import PlutusLedgerApi.V2.Contexts (getContinuingOutputs)
import PlutusTx
import PlutusTx.AsData qualified as PlutusTx
import PlutusTx.Prelude qualified as PlutusTx
import PlutusTx.Show qualified as PlutusTx

-- BLOCK1
data AuctionParams = AuctionParams
  { apSeller  :: PubKeyHash,
    -- ^ Seller's wallet address. The highest bid (if exists) will be sent to the seller.
    -- If there is no bid, the asset auctioned will be sent to the seller.
    apAsset   :: Value,
    -- ^ The asset being auctioned. It can be a single token, multiple tokens of the same
    -- kind, or tokens of different kinds, and the token(s) can be fungible or non-fungible.
    -- These can all be encoded as a `Value`.
    apMinBid  :: Lovelace,
    -- ^ The minimum bid in Lovelace.
    apEndTime :: POSIXTime
    -- ^ The deadline for placing a bid. This is the earliest time the auction can be closed.
  }

PlutusTx.makeLift ''AuctionParams

data Bid = Bid
  { bBidder :: PubKeyHash,
    -- ^ Bidder's wallet address.
    bAmount :: Lovelace
    -- ^ Bid amount in Lovelace.
  }

PlutusTx.deriveShow ''Bid
PlutusTx.unstableMakeIsData ''Bid

instance PlutusTx.Eq Bid where
  {-# INLINEABLE (==) #-}
  bid == bid' =
    bBidder bid PlutusTx.== bBidder bid'
      PlutusTx.&& bAmount bid PlutusTx.== bAmount bid'

-- | Datum represents the state of a smart contract. In this case
-- it contains the highest bid so far (if exists).
newtype AuctionDatum = AuctionDatum { adHighestBid :: Maybe Bid }

PlutusTx.unstableMakeIsData ''AuctionDatum

-- | Redeemer is the input that changes the state of a smart contract.
-- In this case it is either a new bid, or a request to close the auction
-- and pay out the seller and the highest bidder.
data AuctionRedeemer = NewBid Bid | Payout

PlutusTx.unstableMakeIsData ''AuctionRedeemer
-- BLOCK2


{-# INLINEABLE auctionTypedValidator #-}
-- | Given the auction parameters, determines whether the transaction is allowed to
-- spend the UTXO.
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
    sufficientBid (Bid _ amt) = case highestBid of
      Just (Bid _ amt') -> amt PlutusTx.> amt'
      Nothing           -> amt PlutusTx.>= apMinBid params
-- BLOCK4
    validBidTime :: Bool
    validBidTime = to (apEndTime params) `contains` txInfoValidRange txInfo
-- BLOCK5
    refundsPreviousHighestBid :: Bool
    refundsPreviousHighestBid = case highestBid of
      Nothing -> True
      Just (Bid bidder amt) ->
        case PlutusTx.find
          (\o -> txOutAddress o PlutusTx.== pubKeyHashAddress bidder
            PlutusTx.&& txOutValue o PlutusTx.== lovelaceValue amt)
          (txInfoOutputs txInfo) of
          Just _  -> True
          Nothing -> PlutusTx.traceError ("Not found: refund output")
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
        case PlutusTx.find
          ( \o ->
              txOutAddress o PlutusTx.== pubKeyHashAddress (apSeller params)
                PlutusTx.&& txOutValue o PlutusTx.== lovelaceValue amt
          )
          (txInfoOutputs txInfo) of
          Just _  -> True
          Nothing -> PlutusTx.traceError ("Not found: Output paid to seller")

    highestBidderGetsAsset :: Bool
    highestBidderGetsAsset = case highestBid of
      Nothing -> True
      Just (Bid bidder _) ->
        case PlutusTx.find
          ( \o ->
              txOutAddress o PlutusTx.== pubKeyHashAddress bidder
                PlutusTx.&& txOutValue o PlutusTx.== apAsset params
          )
          (txInfoOutputs txInfo) of
          Just _  -> True
          Nothing -> PlutusTx.traceError ("Not found: Output paid to highest bidder")
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
    `PlutusTx.unsafeApplyCode` PlutusTx.liftCode plcVersion100 params
-- BLOCK9
PlutusTx.asData [d|
  data Bid' = Bid'
    { bBidder' :: PubKeyHash,
      -- ^ Bidder's wallet address.
      bAmount' :: Lovelace
      -- ^ Bid amount in Lovelace.
    }
    -- We can derive instances with the newtype strategy, and they
    -- will be based on the instances for 'Data'
    deriving newtype (Eq, Ord, PlutusTx.ToData, FromData, UnsafeFromData)

  -- don't do this for the datum, since it's just a newtype so
  -- simply delegates to the underlying type

  -- | Redeemer is the input that changes the state of a smart contract.
  -- In this case it is either a new bid, or a request to close the auction
  -- and pay out the seller and the highest bidder.
  data AuctionRedeemer' = NewBid' Bid | Payout'
    deriving newtype (Eq, Ord, PlutusTx.ToData, FromData, UnsafeFromData)
  |]
-- BLOCK10
