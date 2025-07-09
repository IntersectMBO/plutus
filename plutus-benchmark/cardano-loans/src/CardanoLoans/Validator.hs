{-# LANGUAGE BangPatterns          #-}
{-# LANGUAGE BlockArguments        #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE MultiWayIf            #-}
{-# LANGUAGE NamedFieldPuns        #-}
{-# LANGUAGE NoImplicitPrelude     #-}
{-# LANGUAGE NumericUnderscores    #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE PatternSynonyms       #-}
{-# LANGUAGE Strict                #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE ViewPatterns          #-}
{-# OPTIONS_GHC -Wno-incomplete-uni-patterns #-}
{-# OPTIONS_GHC -fno-full-laziness #-}
{-# OPTIONS_GHC -fno-ignore-interface-pragmas #-}
{-# OPTIONS_GHC -fno-omit-interface-pragmas #-}
{-# OPTIONS_GHC -fno-spec-constr #-}
{-# OPTIONS_GHC -fno-specialise #-}
{-# OPTIONS_GHC -fno-strictness #-}
{-# OPTIONS_GHC -fno-unbox-small-strict-fields #-}
{-# OPTIONS_GHC -fno-unbox-strict-fields #-}
{-# OPTIONS_GHC -fplugin PlutusTx.Plugin #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:conservative-optimisation #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:no-remove-trace #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:preserve-logging #-}


module CardanoLoans.Validator
(
  LoanDatum(..),
  LoanRedeemer(..),
  BeaconRedeemer(..),
  CurrencySymbol(..),
  TokenName(..),
  PlutusRational,
  POSIXTime(..),
  Slot(..),
  -- pubKeyAsToken,
  tokenAsPubKey,
  adaSymbol,
  adaToken,
  slotToPOSIXTime,
  fromGHC,
  readCurrencySymbol,
  readTokenName,
  readPaymentPubKeyHash,
  unsafeRatio,
  (-),(*),(+),

  loanValidator,
  loanValidatorCode,
  loanValidatorHash,
  loanValidatorScript,

  beaconPolicy,
  beaconPolicyScript,
  beaconPolicySymbol,

  writeData,
  writeScript,
) where

import PlutusTx
import PlutusTx.Prelude
import PlutusTx.Ratio (recip)
import Prelude qualified as Haskell

import PlutusLedgerApi.Data.V3
import PlutusLedgerApi.V1.Data.Value (AssetClass, assetClassValueOf, flattenValue, valueOf)
import PlutusLedgerApi.V3.Data.Contexts (txSignedBy, valueSpent)
import PlutusTx.AssocMap qualified as Map
import PlutusTx.Data.List (List)
import PlutusTx.Data.List qualified as List
-- import Ledger.Address
-- import Plutus.Script.Utils.V2.Scripts as Scripts
-- import Plutus.Script.Utils.V2.Typed.Scripts
-- import Ledger.Bytes (fromHex)
-- import qualified Plutonomy
-- import Ledger.Value (valueOf,flattenValue)
-- import PlutusTx.Numeric as Num
-- import PlutusTx.Ratio as Ratio
-- import PlutusPrelude (foldl')
-- import qualified PlutusTx.AssocMap as Map
-- import Ledger.TimeSlot
-- import Ledger.Slot

-------------------------------------------------
-- Data Types
-------------------------------------------------
data LoanDatum
  -- | The datum for the ask phase.
  = AskDatum
      { askBeacon     :: (CurrencySymbol,TokenName)
      , borrowerId    :: (CurrencySymbol,TokenName)
      , loanAsset     :: (CurrencySymbol,TokenName)
      , loanPrinciple :: Integer
      , loanTerm      :: POSIXTime
      , collateral    :: [(CurrencySymbol,TokenName)]
      }
  -- | The datum for the offer phase.
  | OfferDatum
      { offerBeacon     :: (CurrencySymbol,TokenName)
      , lenderId        :: (CurrencySymbol,TokenName)
      , loanAsset       :: (CurrencySymbol,TokenName)
      , loanPrinciple   :: Integer
      , loanTerm        :: POSIXTime
      , loanInterest    :: Rational
      , loanBacking     :: Integer -- ^ How much of the loan needs to be collateralized. In units of the
                               -- loanAsset.
      , collateralRates :: [((CurrencySymbol,TokenName),Rational)] -- ^ Rates: collateralAsset/loanAsset
      }
  -- | The datum for the active phase. This also has information useful for the credit history.
  | ActiveDatum
      { activeBeacon    :: (CurrencySymbol,TokenName)
      , lenderId        :: (CurrencySymbol,TokenName)
      , borrowerId      :: (CurrencySymbol,TokenName)
      , loanAsset       :: (CurrencySymbol,TokenName)
      , loanPrinciple   :: Integer
      , loanTerm        :: POSIXTime
      , loanInterest    :: Rational
      , loanBacking     :: Integer
      , collateralRates :: [((CurrencySymbol,TokenName),Rational)]
      , loanExpiration  :: POSIXTime
      , loanOutstanding :: Rational
      }

instance Eq LoanDatum where
  {-# INLINABLE (==) #-}
  (AskDatum a b c d e f) == (AskDatum a' b' c' d' e' f') =
    a == a' && b == b' && c == c' && d == d' && e == e' && f == f'
  (OfferDatum a b c d e f g h) == (OfferDatum a' b' c' d' e' f' g' h') =
    a == a' && b == b' && c == c' && d == d' && e == e' && f == f' && g == g' && h == h'
  (ActiveDatum a b c d e f g h i j k) == (ActiveDatum a' b' c' d' e' f' g' h' i' j' k') =
    a == a' && b == b' && c == c' && d == d' && e == e' && f == f' && g == g' && h == h' &&
    i == i' && j == j' && k == k'
  _ == _ = False

data LoanRedeemer
  = CloseAsk
  | CloseOffer
  | AcceptOffer
  | RepayLoan
  | Claim

-- | The redeemer for the beacons.
-- data BeaconRedeemer
--   -- | Mint the ask token to the borrower's address.
--   = MintAskToken PaymentPubKeyHash -- ^ Pubkey for the borrower's staking credential. Simplifies logic.
--   -- | Mint the offer token and lender ID.
--   | MintOfferToken PaymentPubKeyHash -- ^ Pubkey for lender ID.
--   -- | Mint the active token and the borrower ID.
--   -- The first pubkey is the borrower's. The second one is the lender's.
--   | MintActiveToken PaymentPubKeyHash PaymentPubKeyHash
--   -- | Burn any token/IDs.
--   | BurnBeaconToken

-- | A helper type used to create testing beacons.
type AppName = BuiltinString

PlutusTx.unstableMakeIsData ''LoanDatum
PlutusTx.unstableMakeIsData ''LoanRedeemer
-- PlutusTx.unstableMakeIsData ''BeaconRedeemer

-------------------------------------------------
-- Helper Functions
-------------------------------------------------
-- | Used to create a testing set of beacons/IDs without having to change the logic.
app :: AppName
app = "testing"

-- {-# INLINABLE pubKeyAsToken #-}
-- pubKeyAsToken :: PaymentPubKeyHash -> TokenName
-- pubKeyAsToken = TokenName . getPubKeyHash . unPaymentPubKeyHash

{-# INLINABLE tokenAsPubKey #-}
tokenAsPubKey :: TokenName -> PubKeyHash
tokenAsPubKey (TokenName pkh) = PubKeyHash pkh

{-# INLINABLE encodeDatum #-}
-- | This is a convenient way to check what kind of datum it is.
encodeDatum :: LoanDatum -> Integer
encodeDatum AskDatum{}    = 0
encodeDatum OfferDatum{}  = 1
encodeDatum ActiveDatum{} = 2

{-# INLINABLE signed #-}
signed :: [PubKeyHash] -> PubKeyHash -> Bool
signed [] _ = False
signed (k:ks) k'
  | k == k' = True
  | otherwise = signed ks k'

{-# INLINABLE ownInput #-}
ownInput :: ScriptContext -> TxOut
ownInput (ScriptContext info (Spending ref) _) = getScriptInput (txInfoInputs info) ref
ownInput _                                     = traceError "script input error"

{-# INLINABLE getScriptInput #-}
getScriptInput :: [TxInInfo] -> TxOutRef -> TxOut
getScriptInput [] _ = traceError "script input error"
getScriptInput ((TxInInfo iRef ot) : tl) ref
  | iRef == ref = ot
  | otherwise = getScriptInput tl ref

{-# INLINABLE parseLoanDatum #-}
parseLoanDatum :: OutputDatum -> LoanDatum
parseLoanDatum d = case d of
  (OutputDatum (Datum d')) -> unsafeFromBuiltinData d'
  _                        -> traceError "All loan datums must be inline datums."

-- | This is only used by the validator to prevent permanent locking when a staking script
-- is accidentally used. The beacons require that the address uses a staking pubkey.
{-# INLINABLE stakingCredApproves #-}
stakingCredApproves :: Address -> TxInfo -> Bool
stakingCredApproves addr info = case addressStakingCredential addr of
  -- | This is to prevent permanent locking of funds.
  -- The DEX is not meant to be used without a staking credential.
  Nothing -> True

  -- | Check if staking credential signals approval.
  Just stakeCred@(StakingHash cred) -> case cred of
    PubKeyCredential pkh -> signed (txInfoSignatories info) pkh
    ScriptCredential _   -> isJust $ Map.lookup stakeCred $ txInfoWdrl info

  Just _ -> traceError "Wrong kind of staking credential."

-------------------------------------------------
-- On-Chain Loan Validator
-------------------------------------------------
-- | The purpose of this validator is to guarantee that loan negotiations and repayment go
-- smoothly without needing to trust the other party.
--
-- This validator uses the presence or absence of the beacon tokens to judge the validity of
-- the datums. This is due to the beacon tokens only being mintable when the datums are valid.
--
-- If there is ever a datum present WITHOUT the proper beacon token, the staking credential of
-- the address has custody rights. This is to protect the address owner from malicious datums.
-- It is therefore up to the lenders to ensure proper usage of this validator.
--
-- It is technically possible for a malicious user to create their own beacon minting policy for use
-- with this validator. However, this would be an entirely different token than the actual beacons
-- which means they would not even be discoverable by other users.
--
-- Since the active utxo is time-locked for the borrower, there is no need to ensure that ONLY the
-- collateral assets ever leave. Those assets come from the borrower and the borrower has custody
-- of that utxo until the loan expires.
--
-- There are no checks to ensure that the borrower only takes the proper assets from the offer
-- utxo. Instead, it is up to the lender to ONLY deposit the assets that are to be loaned out.
-- This does not seem like an unreasonable expectation.
--
-- The beacon policy requires that the beacons can only be minted to an address with a staking
-- pubkey. However, there is no way to enforce this from the validator's side which means it is
-- possible to send funds to an address instance for this validator that uses a staking script.
-- Note that it would be impossible to actually broadcast this address with the beacons. However,
-- the funds would be permanently locked unless the validator allowed spending with a staking script
-- as well as a staking pubkey. To prevent this locking, the validator still checks if the staking
-- script signals approval, too.
--
-- The interest for these loans is non-compounding.
mkLoan :: LoanDatum -> LoanRedeemer -> ScriptContext -> Bool
mkLoan loanDatum r ctx@ScriptContext{scriptContextTxInfo=info} = case r of
    CloseAsk ->
      -- | The datum must be an AskDatum. This must be checked first since not all fields are the
      -- same across the datum types.
      traceIfFalse "Datum is not an AskDatum" (encodeDatum loanDatum == 0) &&
      -- | The address' staking credential must signal approval. This is required regarless
      -- of whether or not the ask is valid. This is due to the address owner having custody
      -- of invalid utxos.
      traceIfFalse "Staking credential did not approve" stakingCredApproves' &&
      -- | All ask beacons among tx inputs must be burned. This is not meant to be composable
      -- with the other redeemers.
      traceIfFalse "Ask beacons not burned."
        (uncurry (valueOf allVal) (askBeacon loanDatum) ==
           negate (uncurry (valueOf minted) (askBeacon loanDatum)))
    CloseOffer ->
      -- | The datum must be an OfferDatum. This must be checked first since not all fields are the
      -- same across the datum types.
      traceIfFalse "Datum is not an OfferDatum" (encodeDatum loanDatum == 1) &&
      -- | If the offer beacon is present, that means it is a valid offer and the lender has
      -- custody of the utxo. This also means the lender ID is present in the utxo.
      if uncurry (valueOf inputValue) (offerBeacon loanDatum) == 1
      then
        -- | The lender in the lender ID must sign the tx. The ID has the lender's pubkey hash
        -- as the token name.
        traceIfFalse "Lender did not sign"
             (signed (txInfoSignatories info) (tokenAsPubKey $ snd $ lenderId loanDatum)) &&
        -- | All offer beacons in tx inputs must be burned. This is not meant to be composable
        -- with the other redeemers.
        traceIfFalse "Offer beacons not burned"
          (uncurry (valueOf allVal) (offerBeacon loanDatum) ==
           negate (uncurry (valueOf minted) (offerBeacon loanDatum))) &&
        -- | All the lender IDs for this lender in tx inputs must be burned. This is not meant
        -- to be composable with the other redeemers.
        traceIfFalse "Lender IDs not burned"
          (uncurry (valueOf allVal) (lenderId loanDatum) ==
           negate (uncurry (valueOf minted) (lenderId loanDatum)))
      -- | Otherwise the offer is an invalid utxo and the address owner has custody. This also
      -- means no lender IDs are present.
      else
        -- | The staking credential must signal approval.
        traceIfFalse "Staking credential did not approve" stakingCredApproves'
    AcceptOffer ->
      -- | The staking credential must signal approval. The address owner (borrower) is the only
      -- user that can use this redeemer.
      traceIfFalse "Staking credential did not approve" stakingCredApproves' &&
      -- | The following function checks:
      -- 1) There must only be two inputs from this address.
      -- 2) One input must be an ask input (signified by an AskDatum).
      -- 3) One input must be an offer input (signified by an OfferDatum).
      -- 4) The input datums must agree.
      -- 5) The ask input must have the ask beacon.
      -- 6) The offer input must have the offer beacon.
      -- If presence of the beacons signifies that the ask and offer are valid utxos. If either are
      -- invalid, this redeemer will always fail. Invalid ask and offer utxos must be closed with
      -- either the CloseOffer or CloseAsk redeemers. This function will throw error messages
      -- as appropriate.
      validInputs &&
      -- | No other phase beacons are in the tx inputs. Loans must be treated individually
      -- due to how the on-chain credit history works.
      traceIfFalse "No other phase beacons are allowed in tx" noOtherInputBeacons &&
      -- | The following function checks:
      -- 1) There must only be one output to this address - this ensures proper collateral
      --    calculations.
      -- 2) The output must contain the proper datum.
      -- This will throw the proper error message.
      validActiveDatum (parseLoanDatum od) &&
      -- | The required amount of collateral must be posted. The total amount of collateral that
      -- must be posted is determined by the loanBacking field in the OfferDatum.
      traceIfFalse "Not enough collateral posted for loan" enoughCollateral &&
      -- | The following function checks:
      -- 1) The active beacon must be minted and stored in this address.
      -- 2) The borrower ID is minted.
      -- 3) The output contains the active beacon, the lender ID, and the borrower ID.
      -- 4) The ask beacon and the offer beacon are burned.
      -- 5) The ask beacon must have the same currency symbol as the offer beacon.
      -- These checks are actually done by the minting policy. The requirement for the mint
      -- means the minting policy was actually executed.
      traceIfFalse "Active beacon not minted to this address"
        ((valueOf minted (fst $ askBeacon askDatum) (TokenName "Active") == 1) &&
         (valueOf oVal (fst $ askBeacon askDatum) (TokenName "Active") == 1))
    RepayLoan ->
      -- | The input must have an ActiveDatum. This must be checked first since not all fields are
      -- the same across the datum types.
      traceIfFalse "Datum is not an ActiveDatum" (encodeDatum loanDatum == 2) &&
      -- | The staking credential must signal approval. The address owner has custody of the utxo
      -- regardless of whether or not the utxo is a valid loan.
      traceIfFalse "Staking credential did not approve" stakingCredApproves' &&
      -- | If the active beacon is present, this is a valid loan:
      if uncurry (valueOf inputValue) (activeBeacon loanDatum) == 1
      then
        -- | No other beacons are allowed in the tx inputs. This ensures:
        -- 1) There is only one borrower ID present.
        -- 2) There is only one lender ID present.
        -- 3) There is only one valid loan input in tx.
        -- The last point is because treatment of this loan cannot be combined with treatment
        -- of another loan. This is necessary due to the way the on-chain credit history works.
        traceIfFalse "No other phase beacons can be in the tx." noOtherBeacons &&
        -- | No other inputs are allowed from this address. This covers the case of invalid
        -- inputs skewing the repayment calculations.
        traceIfFalse "Only one input allowed from this address" (Haskell.length allAddrInputs == 1) &&
        -- | The loan must not be expired.
        traceIfFalse "Loan is expired" (not $ loanIsExpired $ loanExpiration loanDatum) &&
        -- | There can only be one output to this address. Checked by the next check.
        -- | The output to this address must have the proper datum.
        --     - same as input datum except must subtract loan repaid from loanOutstanding.
        traceIfFalse "Output to address has wrong datum"
          (parseLoanDatum od == loanDatum{loanOutstanding = newOutstanding}) &&
        -- | If new loanOutstanding <= 0, then the loan is fully repaid.
        if newOutstanding <= fromInteger 0
        then
          -- | All collateral is unlocked.
          -- | The only borrower ID in the tx must be burned.
          traceIfFalse "Borrower ID not burned"
            (uncurry (valueOf minted) (borrowerId loanDatum) == -1) &&
          -- | No other tokens can be minted/burned in tx. This is to make checking the credit
          -- history easy since Blockfrost only shows the number of unique tokens minted/burned.
          traceIfFalse "No other tokens can be minted/burned in tx."
            (Haskell.length (flattenValue minted) == 1) &&
          -- | The output to this address must have the active beacon and the lender ID.
          traceIfFalse "Output to address must have active beacon and lender ID"
            (uncurry (valueOf oVal) (lenderId loanDatum) == 1 &&
              uncurry (valueOf oVal) (activeBeacon loanDatum) == 1)
        -- | Otherwise this is a partial payment.
        else
          -- | No collateral can be taken.
          traceIfFalse "No collateral can be taken" noCollateralTaken &&
          -- | The output to this address must have the active beacon, borrower ID, and lender ID.
          traceIfFalse "Output to address must have active beacon, borrower ID, and lender ID"
            (uncurry (valueOf oVal) (lenderId loanDatum) == 1 &&
              uncurry (valueOf oVal) (activeBeacon loanDatum) == 1 &&
              uncurry (valueOf oVal) (borrowerId loanDatum) == 1)
      -- | If the active beacon is missing, this is an invalid loan. The conditions have already
      -- been satisfied:
      -- 1) The datum must be an ActiveDatum.
      -- 2) The staking credential must approve - the address owner has custody of invalid utxos.
      else True
    Claim ->
      -- | The datum must be an ActiveDatum. This must be checked first since not all fields are
      -- the same across the datum types.
      traceIfFalse "Datum is not an ActiveDatum" (encodeDatum loanDatum == 2) &&
      -- | The input utxo must have an active beacon. This also ensures a lender ID is present.
      -- If the active beacon beacon is missing, then this utxo is an invalid loan. The address
      -- owner can claim this utxo using the RepayLoan redeemer.
      traceIfFalse "UTxO does not have an active beacon - use RepayLoan redeemer to claim if address owner"
        (uncurry (valueOf inputValue) (activeBeacon loanDatum) == 1) &&
      -- | There can only be one active beacon in the tx inputs. This is due to how the credit history
      -- works. This also ensures there is only one borrower ID and lender ID in the tx.
      traceIfFalse "No other phase beacons allowed in tx inputs" noOtherBeacons &&
      -- | The loan must either be expired or fully repaid.
      traceIfFalse "Loan is still active" claimable &&
      -- | The active beacon in input must be burned.
      traceIfFalse "Active beacon not burned"
        (uncurry (valueOf minted) (activeBeacon loanDatum) == -1) &&
      -- | The lender ID in input must be burned.
      traceIfFalse "Lender ID not burned"
        (uncurry (valueOf minted) (lenderId loanDatum) == -1) &&
      -- | The lender must sign the tx. Since the active beacon is present, that means the lender has
      -- custody of the utxo as long as the loan is expired. The lender's pubkey hash is the token
      -- name of the lender ID.
      traceIfFalse "Lender did not sign"
        (signed (txInfoSignatories info) (tokenAsPubKey $ snd $ lenderId loanDatum)) &&
      -- | If the borrower ID is still present:
      if uncurry (valueOf inputValue) (borrowerId loanDatum) == 1
      then
        -- | The borrower ID must be burned.
        traceIfFalse "Borrower ID not burned."
          (uncurry (valueOf minted) (borrowerId loanDatum) == -1) &&
        -- | No other tokens can be minted/burned in tx. This is to make checking the credit
        -- history easy since Blockfrost only shows the number of unique tokens minted/burned.
        traceIfFalse "No other tokens can be minted/burned in tx."
          (Haskell.length (flattenValue minted) == 3)
      else
        -- | No other tokens can be minted/burned in tx. This is to make checking the credit
        -- history easy since Blockfrost only shows the number of unique tokens minted/burned.
        traceIfFalse "No other tokens can be minted/burned in tx."
          (Haskell.length (flattenValue minted) == 2)
  where
    -- | Get the credential for this input as well as its value.
    -- Credential is used to check asset flux for address and ensure staking credential approves
    -- when necessary. The value is used to quickly check for beacon tokens.
    (inputCredentials,inputValue) =
      let TxOut{txOutAddress=addr,txOutValue=iVal} = ownInput ctx
      in (addr,iVal)

    -- | This tends to build up a thunk so its evaluation is forced even though it is not always
    -- needed.
    stakingCredApproves' :: Bool
    !stakingCredApproves' = stakingCredApproves inputCredentials info

    -- | The total input value for this tx.
    allVal :: Value
    !allVal = valueSpent info

    minted :: Value
    !minted = txInfoMint info

    -- | Returns a list of inputs from this address.
    allAddrInputs :: [TxOut]
    allAddrInputs =
      let inputs = txInfoInputs info
          foo _ acc [] = acc
          foo iCred !acc (TxInInfo{txInInfoResolved=x@TxOut{txOutAddress=addr}}:xs) =
            if addr == iCred
            then foo iCred (x : acc) xs
            else foo iCred acc xs
      in foo inputCredentials [] inputs

    -- | Get the loan repayment time from the tx's validity range.
    -- It uses to upper bound of the tx's validity range so that a borrower can't
    -- set an earlier time than has already passed to trick the script.
    repaymentTime :: POSIXTime
    repaymentTime = case (\(UpperBound t _) -> t) $ ivTo $ txInfoValidRange info of
      PosInf   -> traceError "invalid-hereafter not specified"
      Finite t -> t
      _        -> traceError "Shouldn't be NegInf."

    -- | Check if the expiration has passed.
    loanIsExpired :: POSIXTime -> Bool
    loanIsExpired endTime = repaymentTime > endTime

    -- | Gets the output to this address.
    -- Throws an error if there is more than one since all redeemers require no more than
    -- one output to this address.
    TxOut{txOutValue=oVal,txOutDatum = od} =
      let outputs = txInfoOutputs info
          foo _ acc [] = acc
          foo iCred !acc (x@TxOut{txOutAddress = addr}:xs) =
            if addr == iCred
            then if Haskell.null acc
                 then foo iCred (x : acc) xs
                 else traceError "There can only be one output to address"
            else foo iCred acc xs
      in case foo inputCredentials [] outputs of
        [x] -> x
        _   -> traceError "Missing output to address"

    -- | The value flux of this address.
    -- Positive values mean the address gained the asset.
    -- Negative values mean the address lost the asset.
    addrDiff :: Value
    addrDiff = oVal <> negate inputValue

    repaidAmount :: Rational
    repaidAmount = fromInteger $ uncurry (valueOf addrDiff) $ loanAsset loanDatum

    -- | Checks that no collateral is taken during RepayLoan (unless loan fully paid off).
    noCollateralTaken :: Bool
    noCollateralTaken =
      let foo _ acc [] = acc
          foo val !acc ((collatAsset,_):xs) =
            foo val (acc && uncurry (valueOf val) collatAsset == 0) xs
      in foo addrDiff True (collateralRates loanDatum)

    -- | This checks that enough collateral is posted when a loan offer is accepted. It uses the
    -- loanBacking to determine validity.
    enoughCollateral :: Bool
    enoughCollateral =
      let target = fromInteger (loanBacking offerDatum)
          foo _ acc [] = acc
          foo val !acc ((collatAsset,price):xs) =
            foo val
                (acc + fromInteger (uncurry (valueOf val) collatAsset) * recip price)
                xs
      in foo oVal (fromInteger 0) (collateralRates offerDatum) >= target

    -- | New total of loan outstanding.
    newOutstanding :: Rational
    newOutstanding = loanOutstanding loanDatum - repaidAmount

    -- | This will throw an error if there are not only two inputs or if the two inputs are not
    -- an ask input and an offer input.
    (askVal,askDatum,offerVal,offerDatum) =
      case allAddrInputs of
        [TxOut{txOutDatum=xd,txOutValue=xVal},TxOut{txOutDatum=yd,txOutValue=yVal}] ->
          let xd' = parseLoanDatum xd
              yd' = parseLoanDatum yd
          in if encodeDatum xd' == 0 && encodeDatum yd' == 1 then (xVal,xd',yVal,yd')
             else if encodeDatum xd' == 1 && encodeDatum yd' == 0 then (yVal,yd',xVal,xd')
             else traceError "Inputs are not the right phases"
        _ -> traceError "There must be two and only two inputs from this address"

    -- | Ensures that the borrower and lender are agreeing to the same loan.
    datumsAgree :: Bool
    datumsAgree
      | fst (askBeacon askDatum) /= fst (offerBeacon offerDatum) =
          traceError "Datums are using different beacons"
      | loanAsset askDatum /= loanAsset offerDatum =
          traceError "Datums have different loan assets"
      | loanPrinciple askDatum /= loanPrinciple offerDatum =
          traceError "Datums have different loan principles"
      | loanTerm askDatum /= loanTerm offerDatum =
          traceError "Datums have different loan terms"
      | collateral askDatum /= Haskell.map fst (collateralRates offerDatum) =
          traceError "Datums have different collateral assets"
      | otherwise = True

    -- | Checks that the datums agree and the proper beacons are present.
    validInputs :: Bool
    validInputs = datumsAgree &&
      traceIfFalse "Ask beacon is missing" (uncurry (valueOf askVal) (askBeacon askDatum) == 1) &&
      traceIfFalse "Offer beacon is missing" (uncurry (valueOf offerVal) (offerBeacon offerDatum) == 1)

    -- | This is only used with AcceptLoan.
    noOtherInputBeacons :: Bool
    noOtherInputBeacons =
      let beaconSym' = fst $ offerBeacon offerDatum
      in valueOf allVal beaconSym' (TokenName "Ask") == 1 &&
         valueOf allVal beaconSym' (TokenName "Offer") == 1 &&
         valueOf allVal beaconSym' (TokenName "Active") == 0

    -- | This is only used with the RepayLoan and Claim. This ensures all loans are treated separately.
    noOtherBeacons :: Bool
    noOtherBeacons =
      let beaconSym' = fst $ activeBeacon loanDatum
      in valueOf allVal beaconSym' (TokenName "Ask") == 0 &&
         valueOf allVal beaconSym' (TokenName "Offer") == 0 &&
         valueOf allVal beaconSym' (TokenName "Active") == 1

    -- | Get the loan start time from the tx's validity range. Based off the lower bound.
    -- This is also used when a lender is claiming a loan.
    startTime :: POSIXTime
    startTime = case (\(LowerBound t _) -> t) $ ivFrom $ txInfoValidRange info of
      NegInf   -> traceError "invalid-before not specified"
      Finite x -> x
      _        -> traceError "Shouldn't be PosInf."

    expirationTime :: POSIXTime
    expirationTime = startTime + loanTerm offerDatum

    -- | Ensures the new active datum has the proper information.
    validActiveDatum :: LoanDatum -> Bool
    validActiveDatum AskDatum{} = traceError "Output datum not ActiveDatum"
    validActiveDatum OfferDatum{} = traceError "Output datum not ActiveDatum"
    validActiveDatum newDatum
      | activeBeacon newDatum /= (fst $ askBeacon askDatum,TokenName "Active") =
          traceError "Active datum activeBeacon incorrect"
      | lenderId newDatum /= lenderId offerDatum =
          traceError "Active datum lenderId incorrect"
      | borrowerId newDatum /= borrowerId askDatum =
          traceError "Active datum borrowerId incorrect"
      | loanAsset newDatum /= loanAsset askDatum =
          traceError "Active datum loanAsset incorrect"
      | loanPrinciple newDatum /= loanPrinciple askDatum =
          traceError "Active datum loanPrinciple incorrect"
      | loanTerm newDatum /= loanTerm askDatum =
          traceError "Active Datum loanTerm incorrect"
      | loanInterest newDatum /= loanInterest offerDatum =
          traceError "Active datum loanInterest incorrect"
      | loanBacking newDatum /= loanBacking offerDatum =
          traceError "Active datum loanBacking incorrect"
      | collateralRates newDatum /= collateralRates offerDatum =
          traceError "Active datum collateralRates incorrect"
      | loanExpiration newDatum /= expirationTime =
          traceError "Active datum loanExpiration /= ttl + loanTerm"
      | loanOutstanding newDatum /=
          fromInteger (loanPrinciple askDatum) * (fromInteger 1 + loanInterest offerDatum) =
            traceError "Active datum loanOutstanding incorrect"
      | otherwise = True

    -- | Allows claiming early if loan is fully repaid. Get's current time from TTL.
    claimable :: Bool
    claimable = startTime >= loanExpiration loanDatum ||
                loanOutstanding loanDatum <= fromInteger 0

loanValidatorCode :: CompiledCode (BuiltinData -> BuiltinUnit)
loanValidatorCode = $$(compile [||untypedValidator||])
  where
    typedValidator :: ScriptContext -> Bool
    typedValidator context = trace "Validation completed" $ mkLoan loanDatum loanRedeemer context
      where
        loanDatum :: LoanDatum
        loanDatum = do
          let SpendingScript _ (Just (Datum datum)) = scriptContextScriptInfo context
          unsafeFromBuiltinData datum

        loanRedeemer :: LoanRedeemer
        loanRedeemer =
          case fromBuiltinData (getRedeemer (scriptContextRedeemer context)) of
            Nothing -> traceError "Failed to parse Redeemer"
            Just r  -> trace "Parsed Redeemer" r

    untypedValidator :: BuiltinData -> BuiltinUnit
    untypedValidator scriptContextData =
      case trace "Parsing ScriptContext..." (fromBuiltinData scriptContextData) of
        Nothing  -> traceError "Failed to parse ScriptContext"
        Just ctx -> check $ typedValidator $ trace "Parsed ScriptContext" ctx

-- -------------------------------------------------
-- -- On-Chain Beacon Policy
-- -------------------------------------------------
-- mkBeaconPolicy :: AppName -> ValidatorHash  -- ^ Extra parameters
--                -> BeaconRedeemer -> ScriptContext -> Bool
-- mkBeaconPolicy appName dappHash r ctx@ScriptContext{scriptContextTxInfo = info} = case r of
--     MintAskToken (PaymentPubKeyHash pkh) ->
--       -- | Only one beacon token can be minted this tx and it must have the token name "Ask".
--       mintCheck r &&
--       -- | The following function checks:
--       -- 1) Must be minted to an address protected by the dappHash.
--       -- 2) Must be minted to an address with a staking pubkey matching the supplied pubkey.
--       -- 3) The ask token must be stored with the proper ask datum.
--       --     - askBeacon == (beaconSym, TokenName "Ask")
--       --     - borrowerId == (beaconSym,pubkeyAsToken pkh)
--       --     - loanPrinciple > 0
--       --     - loanTerm > 0
--       --     - collateral list not empty
--       destinationCheck r &&
--       -- | The receiving staking pubkey must sign.
--       traceIfFalse "Receiving staking pubkey did not sign" (signed (txInfoSignatories info) pkh)
--     MintOfferToken (PaymentPubKeyHash pkh) ->
--       -- | The following function checks:
--       -- 1) Must mint exactly one offer token and exactly one lender ID.
--       -- 2) The offer token must have the token name "Offer".
--       -- 3) The lender token must have the lender's pubkey as its token name.
--       mintCheck r &&
--       -- | The following function checks:
--       -- 1) Must be minted to an address protected by the dappHash.
--       -- 2) Must be minted to an address with a staking pubkey.
--       -- 3) The offer token and lender ID must be stored in the same utxo at the dapp address.
--       -- 4) The tokens must be stored with the proper offer datum.
--       --     - offerBeacon == (beaconSym,TokenName "Offer")
--       --     - lenderId == (beaconSym,pubKeyAsToken pkh)
--       --     - loanPrinciple > 0.
--       --     - loanTerm > 0.
--       --     - loanInterest > 0.
--       --     - loanBacking > 0.
--       --     - collateralRates not null
--       --     - all collaterale rates > 0.
--       -- 5) The offer token must be stored with the amount of the loan asset specified in
--       -- the datum. If the loan asset is ADA, an additional 3 ADA is required to account for
--       -- the presence of the beacon tokens.
--       destinationCheck r &&
--       -- | The lender pkh must sign the tx.
--       traceIfFalse "Lender did not sign tx" (signed (txInfoSignatories info) pkh)
--     MintActiveToken _ _ ->
--       -- | The following function checks:
--       -- 1) Both the ask token and the offer token must be burned in the tx.
--       -- 2) Must mint exactly one active token and one borrower ID.
--       -- 3) The active token must have the token name "Active".
--       -- 4) The borrower ID must have the borrower's pubkey as the token name.
--       mintCheck r &&
--       -- | The active token, the borrower ID, and the lender ID (from the offer input) must
--       -- be stored in the same utxo at the dapp address using the supplied staking pubkey.
--       destinationCheck r
--     BurnBeaconToken ->
--       -- | Allowed as long as redeemer only used to burn.
--       mintCheck r
--   where
--     beaconSym :: CurrencySymbol
--     beaconSym = ownCurrencySymbol ctx

--     minted :: Value
--     minted = txInfoMint info

--     -- | Returns only the beacons minted/burned. This is useful for ensuring only
--     -- the required beacons are minting.
--     beaconMint :: [(CurrencySymbol,TokenName,Integer)]
--     beaconMint = case Map.lookup beaconSym $ getValue minted of
--       Nothing -> traceError "MintError"
--       Just bs -> flattenValue $ Value $ Map.insert beaconSym bs Map.empty -- ^ a Value with only beacons

--     mintSatisfied :: TokenName -> Integer -> [(CurrencySymbol,TokenName,Integer)] -> Bool
--     mintSatisfied _ _ [] = False
--     mintSatisfied tn n ((_,tn',n'):cs)
--       | tn == tn' && n == n' = True
--       | otherwise = mintSatisfied tn n cs

--     mintCheck :: BeaconRedeemer -> Bool
--     mintCheck r' = case (r',beaconMint) of
--       (MintAskToken _, [(_,tn,n)]) ->
--         traceIfFalse "Only the ask beacon must have the token name 'Ask'" (tn == TokenName "Ask") &&
--         traceIfFalse "Only one ask beacon can be minted" (n == 1)
--       (MintAskToken _, _) ->
--         traceError "Only one beacon can be minted and it must be the ask beacon."
--       (MintOfferToken pkh, [(_,tn1,n1),(_,tn2,n2)]) ->
--         if tn1 == TokenName "Offer" then
--           traceIfFalse "Only one offer beacon can be minted" (n1 == 1) &&
--           traceIfFalse "The lender ID does not have the lender's pubkey as token name"
--             (tn2 == pubKeyAsToken pkh) &&
--           traceIfFalse "Only one lender ID can be minted" (n2 == 1)
--         else if tn2 == TokenName "Offer" then
--           traceIfFalse "Only one offer beacon can be minted" (n2 == 1) &&
--           traceIfFalse "The lender ID does not have the lender's pubkey as token name"
--             (tn1 == pubKeyAsToken pkh) &&
--           traceIfFalse "Only one lender ID can be minted" (n1 == 1)
--         else traceError "Only thhe offer beacon and lender ID can be minted"
--       (MintOfferToken _, _) ->
--         traceError "Only the offer beacon and lender ID can be minted"
--       (MintActiveToken pkh _, xs@[_,_,_,_]) ->
--         traceIfFalse "One ask beacon not burned" (mintSatisfied (TokenName "Ask") (-1) xs) &&
--         traceIfFalse "One offer beacon not burned" (mintSatisfied (TokenName "Offer") (-1) xs) &&
--         traceIfFalse "One active beacon not minted" (mintSatisfied (TokenName "Active") 1 xs) &&
--         traceIfFalse "One borrower ID not minted" (mintSatisfied (pubKeyAsToken pkh) 1 xs)
--       (MintActiveToken _ _, _) ->
--         traceError
--           "The offer and ask beacon must be burned while the active beacon and borrower ID must be minted"
--       (BurnBeaconToken, xs) ->
--         traceIfFalse "Beacons can only be burned with this redeemer" (all (\(_,_,n) -> n < 0) xs)

--     -- | A helper function for destinationCheck to make the code easier to reason about.
--     -- This uses the appName in the error message.
--     validDestination :: ValidatorHash -> Bool
--     validDestination spendVh
--       | spendVh /= dappHash =
--           traceError ("Beacon not minted to the proper " <> appName <> " address")
--       | otherwise = True

--     validDatum :: BeaconRedeemer -> LoanDatum -> Bool
--     validDatum (MintAskToken pkh) (AskDatum ab bi _ lq lt c)
--       | ab /= (beaconSym,TokenName "Ask") = traceError "Invalid AskDatum askBeacon"
--       | bi /= (beaconSym,pubKeyAsToken pkh) = traceError "Invalid AskDatum borrowerId"
--       | lq <= 0 = traceError "AskDatum loanPrinciple not > 0"
--       | lt <= 0 = traceError "AskDatum loanTerm not > 0"
--       | null c = traceError "AskDatum collateral is empty"
--       | otherwise = True
--     validDatum (MintAskToken _) _ = traceError "Ask beacon not stored with an AskDatum"
--     validDatum (MintOfferToken pkh) (OfferDatum ob li _ lq lt i dp cr)
--       | ob /= (beaconSym, TokenName "Offer") = traceError "Invalid OfferDatum offerBeacon"
--       | li /= (beaconSym, pubKeyAsToken pkh) = traceError "OfferDatum lenderId not correct"
--       | lq <= 0 = traceError "OfferDatum loanPrinciple not > 0"
--       | lt <= 0 = traceError "OfferDatum loanTerm not > 0"
--       | i <= fromInteger 0 = traceError "OfferDatum loanInterest not > 0"
--       | dp <= 0 = traceError "OfferDatum loanBacking not > 0"
--       | null cr = traceError "OfferDatum collateralRates is empty"
--       | not $ all (\(_,p) -> p > fromInteger 0) cr = traceError "All collateralRates must be > 0"
--       | otherwise = True
--     validDatum (MintOfferToken _) _ = traceError "Offer beacon not stored with an OfferDatum"
--     validDatum _ _ = True -- ^ This is to stop the pattern match compile warning. It is not used
--                           --   for any other redeemers.

--     -- | This checks that the offer beacon is stored with the desired loan amount.
--     loanPrincipleMet :: Value -> LoanDatum -> Bool
--     loanPrincipleMet oVal d
--       | loanAsset d == (adaSymbol,adaToken) =
--           uncurry (valueOf oVal) (loanAsset d) >= loanPrinciple d + 3_000_000
--       | otherwise = uncurry (valueOf oVal) (loanAsset d) >= loanPrinciple d

--     -- | Check if the beacons are going to the proper address and are stored properly (together and
--     -- with proper datum). This is only used for MintOfferToken and MintAskToken.
--     destinationCheck :: BeaconRedeemer -> Bool
--     destinationCheck r' =
--       let outputs = txInfoOutputs info
--           foo acc TxOut{txOutDatum=d
--                        ,txOutValue=oVal
--                        ,txOutAddress=Address{addressCredential=addrCred
--                                             ,addressStakingCredential=maybeStakeCred
--                                             }
--                        } =
--             case r' of
--               MintAskToken (PaymentPubKeyHash pkh)->
--                 if valueOf oVal beaconSym (TokenName "Ask") == 1 then
--                   case (addrCred,maybeStakeCred) of
--                     (ScriptCredential vh, Just (StakingHash (PubKeyCredential pkh'))) ->
--                       -- | validDestination and validDatum will both fail with traceError
--                       -- unless True.
--                       acc && validDestination vh &&
--                       validDatum r' (parseLoanDatum d) &&
--                       traceIfFalse "Receiving address does not match redeemer pubkey hash" (pkh == pkh')
--                     _ -> traceError "Ask beacon must go to a dapp address using a staking pubkey"
--                 else acc
--               MintOfferToken pkh ->
--                 if valueOf oVal beaconSym (TokenName "Offer") == 1 then
--                   if valueOf oVal beaconSym (pubKeyAsToken pkh) == 1 then
--                     case (addrCred,maybeStakeCred) of
--                       (ScriptCredential vh, Just (StakingHash (PubKeyCredential _))) ->
--                         -- | validDestination and validDatum will both fail with traceError
--                         -- unless True.
--                         let datum = parseLoanDatum d
--                         in
--                           acc && validDestination vh && validDatum r' datum &&
--                           traceIfFalse "Offer beacon not stored with required loan amount"
--                             (loanPrincipleMet oVal datum)
--                       _ -> traceError "Offer beacon must go to a dapp address using a staking pubkey"
--                   else traceError "Offer token and lender ID must be stored in the same utxo."
--                 else acc
--               MintActiveToken borrowerPkh@(PaymentPubKeyHash pkh) lenderPkh ->
--                 if valueOf oVal beaconSym (TokenName "Active") == 1 then
--                   if valueOf oVal beaconSym (pubKeyAsToken borrowerPkh) == 1 then
--                     if valueOf oVal beaconSym (pubKeyAsToken lenderPkh) == 1 then
--                       case (addrCred,maybeStakeCred) of
--                         (ScriptCredential vh, Just (StakingHash (PubKeyCredential pkh'))) ->
--                           -- | validDestination will fail with traceError unless True.
--                           acc && validDestination vh && pkh == pkh'
--                         _ -> traceError
--                           "Active token must go to the dapp address using the supplied staking pubkey"
--                     else traceError "Lender ID not stored with borrower ID and active beacon"
--                   else traceError "Borrower ID not stored with active beacon"
--                 else acc
--               _ -> False
--       in foldl' foo True outputs


-- beaconPolicy :: MintingPolicy
-- beaconPolicy = Plutonomy.optimizeUPLC $ mkMintingPolicyScript
--   ($$(PlutusTx.compile [|| wrap ||])
--     `PlutusTx.applyCode` PlutusTx.liftCode app
--     `PlutusTx.applyCode` PlutusTx.liftCode loanValidatorHash)
--   where
--     wrap x y = mkUntypedMintingPolicy $ mkBeaconPolicy x y

-- beaconPolicyScript :: Script
-- beaconPolicyScript = unMintingPolicyScript beaconPolicy

-- beaconPolicySymbol :: CurrencySymbol
-- beaconPolicySymbol = scriptCurrencySymbol beaconPolicy
