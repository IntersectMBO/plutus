{-# LANGUAGE DataKinds                  #-}
{-# LANGUAGE DeriveAnyClass             #-}
{-# LANGUAGE DeriveGeneric              #-}
{-# LANGUAGE DerivingStrategies         #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ImportQualifiedPost        #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE NoImplicitPrelude          #-}
{-# LANGUAGE OverloadedStrings          #-}
{-# LANGUAGE PatternSynonyms            #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE Strict                     #-}
{-# LANGUAGE TemplateHaskell            #-}
{-# LANGUAGE TypeApplications           #-}
{-# LANGUAGE UndecidableInstances       #-}
{-# LANGUAGE ViewPatterns               #-}
{-# OPTIONS_GHC -fno-full-laziness #-}
{-# OPTIONS_GHC -fno-ignore-interface-pragmas #-}
{-# OPTIONS_GHC -fno-omit-interface-pragmas #-}
{-# OPTIONS_GHC -fno-spec-constr #-}
{-# OPTIONS_GHC -fno-specialise #-}
{-# OPTIONS_GHC -fno-strictness #-}
{-# OPTIONS_GHC -fno-unbox-small-strict-fields #-}
{-# OPTIONS_GHC -fno-unbox-strict-fields #-}
{-# OPTIONS_GHC -fplugin PlutusTx.Plugin #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:target-version=1.1.0 #-}

module AuctionValidator where

import GHC.Generics (Generic)

import PlutusTx.Prelude

import PlutusLedgerApi.V1 (lovelaceValueOf, toPubKeyHash, valueOf)
import PlutusLedgerApi.V1.Interval (contains)
import PlutusLedgerApi.V3 (CurrencySymbol, Datum (Datum, getDatum), Lovelace,
                           OutputDatum (NoOutputDatum, OutputDatum, OutputDatumHash), POSIXTime,
                           PubKeyHash, Redeemer (getRedeemer), ScriptContext (..),
                           ScriptInfo (SpendingScript), TokenName,
                           TxInfo (txInfoOutputs, txInfoValidRange),
                           TxOut (txOutAddress, txOutDatum, txOutValue), from, to)
import PlutusLedgerApi.V3.Contexts (getContinuingOutputs)
import PlutusTx (CompiledCode, FromData (..), ToData, UnsafeFromData (..), compile, liftCodeDef,
                 makeIsDataSchemaIndexed, makeLift, unsafeApplyCode)
import PlutusTx.AsData qualified as PlutusTx
import PlutusTx.Blueprint (HasBlueprintDefinition, definitionRef)
import PlutusTx.List qualified as List
import PlutusTx.Prelude qualified as PlutusTx
import PlutusTx.Show qualified as PlutusTx

-- BLOCK1
-- AuctionValidator.hs
data AuctionParams = AuctionParams
  { apSeller         :: PubKeyHash
  -- ^ Seller's public key hash. The highest bid (if exists) will be sent to the seller.
  -- If there is no bid, the asset auctioned will be sent to the seller.
  , apCurrencySymbol :: CurrencySymbol
  -- ^ The currency symbol of the token being auctioned.
  , apTokenName      :: TokenName
  -- ^ The name of the token being auctioned.
  -- These can all be encoded as a `Value`.
  , apMinBid         :: Lovelace
  -- ^ The minimum bid in Lovelace.
  , apEndTime        :: POSIXTime
  -- ^ The deadline for placing a bid. This is the earliest time the auction can be closed.
  }
  deriving stock (Generic)
  deriving anyclass (HasBlueprintDefinition)

PlutusTx.makeLift ''AuctionParams
PlutusTx.makeIsDataSchemaIndexed ''AuctionParams [('AuctionParams, 0)]

data Bid = Bid
  { bAddr   :: PlutusTx.BuiltinByteString
  -- ^ Bidder's wallet address
  , bPkh    :: PubKeyHash
  -- ^ Bidder's public key hash.
  , bAmount :: Lovelace
  -- ^ Bid amount in Lovelace.
  }
  deriving stock (Generic)
  deriving anyclass (HasBlueprintDefinition)

PlutusTx.deriveShow ''Bid
PlutusTx.makeIsDataSchemaIndexed ''Bid [('Bid, 0)]

instance PlutusTx.Eq Bid where
  {-# INLINEABLE (==) #-}
  bid == bid' =
    bPkh bid
      PlutusTx.== bPkh bid'
      PlutusTx.&& bAmount bid
      PlutusTx.== bAmount bid'

{- | Datum represents the state of a smart contract. In this case
it contains the highest bid so far (if exists).
-}
newtype AuctionDatum = AuctionDatum {adHighestBid :: Maybe Bid}
  deriving stock (Generic)
  deriving newtype
    ( HasBlueprintDefinition
    , PlutusTx.ToData
    , PlutusTx.FromData
    , PlutusTx.UnsafeFromData
    )

{- | Redeemer is the input that changes the state of a smart contract.
In this case it is either a new bid, or a request to close the auction
and pay out the seller and the highest bidder.
-}
data AuctionRedeemer = NewBid Bid | Payout
  deriving stock (Generic)
  deriving anyclass (HasBlueprintDefinition)

PlutusTx.makeIsDataSchemaIndexed ''AuctionRedeemer [('NewBid, 0), ('Payout, 1)]

-- BLOCK2
-- AuctionValidator.hs
{-# INLINEABLE auctionTypedValidator #-}

{- | Given the auction parameters, determines whether the transaction is allowed to
spend the UTXO.
-}
auctionTypedValidator ::
  AuctionParams ->
  AuctionDatum ->
  AuctionRedeemer ->
  ScriptContext ->
  Bool
auctionTypedValidator params (AuctionDatum highestBid) redeemer ctx = List.and conditions
  where
    conditions :: [Bool]
    conditions = case redeemer of
      NewBid bid ->
        [ -- The new bid must be higher than the highest bid.
          -- If this is the first bid, it must be at least as high as the minimum bid.
          sufficientBid bid
        , -- The bid is not too late.
          validBidTime
        , -- The previous highest bid should be refunded.
          refundsPreviousHighestBid
        , -- A correct new datum is produced, containing the new highest bid.
          correctOutput bid
        ]
      Payout ->
        [ -- The payout is not too early.
          validPayoutTime
        , -- The seller gets the highest bid.
          sellerGetsHighestBid
        , -- The highest bidder gets the asset.
          highestBidderGetsAsset
        ]
-- BLOCK3
-- AuctionValidator.hs
    sufficientBid :: Bid -> Bool
    sufficientBid (Bid _ _ amt) = case highestBid of
      Just (Bid _ _ amt') -> amt PlutusTx.> amt'
      Nothing             -> amt PlutusTx.>= apMinBid params
-- BLOCK4
-- AuctionValidator.hs
    validBidTime :: Bool
    ~validBidTime = to (apEndTime params) `contains` txInfoValidRange (scriptContextTxInfo ctx)
-- BLOCK5
-- AuctionValidator.hs
    refundsPreviousHighestBid :: Bool
    ~refundsPreviousHighestBid = case highestBid of
      Nothing -> True
      Just (Bid _ bidderPkh amt) ->
        case List.find
          ( \o ->
              (toPubKeyHash (txOutAddress o) PlutusTx.== Just bidderPkh)
                PlutusTx.&& (lovelaceValueOf (txOutValue o) PlutusTx.== amt)
          )
          (txInfoOutputs (scriptContextTxInfo ctx)) of
          Just _  -> True
          Nothing -> PlutusTx.traceError "Not found: refund output"
-- BLOCK6
-- AuctionValidator.hs
    currencySymbol :: CurrencySymbol
    currencySymbol = apCurrencySymbol params

    tokenName :: TokenName
    tokenName = apTokenName params

    correctOutput :: Bid -> Bool
    correctOutput bid = case getContinuingOutputs ctx of
      [o] ->
        let correctOutputDatum = case txOutDatum o of
              OutputDatum (Datum newDatum) -> case PlutusTx.fromBuiltinData newDatum of
                Just (AuctionDatum (Just bid')) ->
                  PlutusTx.traceIfFalse
                    "Invalid output datum: contains a different Bid than expected"
                    (bid PlutusTx.== bid')
                Just (AuctionDatum Nothing) ->
                  PlutusTx.traceError "Invalid output datum: expected Just Bid, got Nothing"
                Nothing ->
                  PlutusTx.traceError "Failed to decode output datum"
              OutputDatumHash _ ->
                PlutusTx.traceError "Expected OutputDatum, got OutputDatumHash"
              NoOutputDatum ->
                PlutusTx.traceError "Expected OutputDatum, got NoOutputDatum"

            outValue = txOutValue o

            correctOutputValue =
              (lovelaceValueOf outValue PlutusTx.== bAmount bid)
                PlutusTx.&& (valueOf outValue currencySymbol tokenName PlutusTx.== 1)
         in correctOutputDatum PlutusTx.&& correctOutputValue
      os ->
        PlutusTx.traceError
          ( "Expected exactly one continuing output, got "
              PlutusTx.<> PlutusTx.show (List.length os)
          )
-- BLOCK7
-- AuctionValidator.hs
    validPayoutTime :: Bool
    ~validPayoutTime = from (apEndTime params) `contains` txInfoValidRange (scriptContextTxInfo ctx)

    sellerGetsHighestBid :: Bool
    ~sellerGetsHighestBid = case highestBid of
      Nothing -> True
      Just bid ->
        case List.find
          ( \o ->
              (toPubKeyHash (txOutAddress o) PlutusTx.== Just (apSeller params))
                PlutusTx.&& (lovelaceValueOf (txOutValue o) PlutusTx.== bAmount bid)
          )
          (txInfoOutputs (scriptContextTxInfo ctx)) of
          Just _  -> True
          Nothing -> PlutusTx.traceError "Not found: Output paid to seller"

    highestBidderGetsAsset :: Bool
    ~highestBidderGetsAsset =
      let highestBidder = case highestBid of
            -- If there are no bids, the asset should go back to the seller
            Nothing  -> apSeller params
            Just bid -> bPkh bid
       in case List.find
            ( \o ->
                (toPubKeyHash (txOutAddress o) PlutusTx.== Just highestBidder)
                  PlutusTx.&& (valueOf (txOutValue o) currencySymbol tokenName PlutusTx.== 1)
            )
            (txInfoOutputs (scriptContextTxInfo ctx)) of
            Just _  -> True
            Nothing -> PlutusTx.traceError "Not found: Output paid to highest bidder"

-- BLOCK8
-- AuctionValidator.hs
auctionUntypedValidator :: AuctionParams -> BuiltinData -> BuiltinUnit
auctionUntypedValidator params ctx =
  PlutusTx.check (auctionTypedValidator params auctionDatum auctionRedeemer scriptContext)
  where
    scriptContext :: ScriptContext
    scriptContext = PlutusTx.unsafeFromBuiltinData ctx

    auctionDatum :: AuctionDatum
    auctionDatum =
      case scriptContextScriptInfo scriptContext of
        SpendingScript _TxOutRef (Just datum) -> PlutusTx.unsafeFromBuiltinData (getDatum datum)
        _ -> PlutusTx.traceError "Expected SpendingScript with a datum"

    auctionRedeemer :: AuctionRedeemer
    auctionRedeemer =
      PlutusTx.unsafeFromBuiltinData (getRedeemer (scriptContextRedeemer scriptContext))

{-# INLINEABLE auctionUntypedValidator #-}

auctionValidatorScript :: AuctionParams -> CompiledCode (BuiltinData -> BuiltinUnit)
auctionValidatorScript params =
  $$(PlutusTx.compile [||auctionUntypedValidator||])
    `PlutusTx.unsafeApplyCode` liftCodeDef params

-- BLOCK9
-- AuctionValidator.hs
PlutusTx.asData
  [d|
    data Bid' = Bid'
      { bPkh' :: PubKeyHash
      , -- \^ Bidder's wallet address.
        bAmount' :: Lovelace
      }
      -- \^ Bid amount in Lovelace.

      -- We can derive instances with the newtype strategy, and they
      -- will be based on the instances for 'Data'
      deriving newtype (Eq, ToData, FromData, UnsafeFromData)

    -- don't do this for the datum, since it's just a newtype so
    -- simply delegates to the underlying type

    -- \| Redeemer is the input that changes the state of a smart contract.
    -- In this case it is either a new bid, or a request to close the auction
    -- and pay out the seller and the highest bidder.
    data AuctionRedeemer' = NewBid' Bid | Payout'
      deriving newtype (Eq, ToData, FromData, UnsafeFromData)
    |]

-- BLOCK10
-- AuctionValidator.hs
