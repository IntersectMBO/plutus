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
{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE ViewPatterns          #-}
{-# OPTIONS_GHC -Wno-unused-local-binds #-}
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
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:no-conservative-optimisation #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:no-remove-trace #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:preserve-logging #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:datatypes=BuiltinCasing #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Redundant if" #-}


module CardanoLoans.Validator
(
  LoanDatum(..),
  LoanRedeemer(..),
  CurrencySymbol(..),
  TokenName(..),
  POSIXTime(..),
  tokenAsPubKey,
  adaSymbol,
  adaToken,
  fromHaskellRatio,
  unsafeRatio,
  (-),(*),(+),
  loanValidatorCode,
) where

import PlutusLedgerApi.V1.Value (valueOf)
import PlutusLedgerApi.V3
import PlutusLedgerApi.V3.Contexts (valueSpent)
import PlutusTx
import PlutusTx.AssocMap qualified as Map
import PlutusTx.List qualified as List
import PlutusTx.Prelude

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

-- | A helper type used to create testing beacons.
type AppName = BuiltinString

PlutusTx.unstableMakeIsData ''LoanDatum
PlutusTx.unstableMakeIsData ''LoanRedeemer

-------------------------------------------------
-- Helper Functions
-------------------------------------------------
-- | Used to create a testing set of beacons/IDs without having to change the logic.
app :: AppName
app = "testing"

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
ownInput (ScriptContext info _ (SpendingScript ref _)) = getScriptInput (txInfoInputs info) ref
ownInput _                                             = traceError "script input error ownInput"

{-# INLINABLE getScriptInput #-}
getScriptInput :: [TxInInfo] -> TxOutRef -> TxOut
getScriptInput [] _ = traceError "script input error getScriptInput"
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
  Just (StakingHash cred) -> case cred of
    PubKeyCredential pkh -> signed (txInfoSignatories info) pkh
    ScriptCredential _   -> isJust $ Map.lookup cred $ txInfoWdrl info

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
mkLoan loanDatum r ctx =
    case r of
      CloseAsk ->
        -- | The datum must be an AskDatum. This must be checked first since not all fields are the
        -- same across the datum types.
        traceIfFalse "Datum is not an AskDatum" (encodeDatum loanDatum == 0) &&
        -- | The address' staking credential must signal approval. This is required regardless
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
      _ ->
        True
  where
    ScriptContext{scriptContextTxInfo=info} = ctx

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
    !minted = mintValueMinted (txInfoMint info)

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
          foo iCred !acc (x'@TxOut{txOutAddress = addr}:xs') = do
            let x = x'
            let xs = xs'
            if addr == iCred
            then if List.null acc
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


loanValidatorCode :: CompiledCode (BuiltinData -> BuiltinUnit)
loanValidatorCode = $$(compile [||untypedValidator||])
  where
    typedValidator :: ScriptContext -> Bool
    typedValidator context = trace "Validation completed" $ mkLoan loanDatum loanRedeemer context
      where
        loanDatum :: LoanDatum
        loanDatum = do
          let SpendingScript _ (Just (Datum datum)) = scriptContextScriptInfo context
          case fromBuiltinData datum of
            Nothing -> traceError "Failed to parse Datum"
            Just r  -> trace "Parsed Datum" r

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
