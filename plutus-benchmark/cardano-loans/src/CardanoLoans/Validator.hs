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
{-# LANGUAGE TypeApplications      #-}
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
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:no-conservative-optimisation #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:no-remove-trace #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:preserve-logging #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Redundant if" #-}


module CardanoLoans.Validator
(
  LoanDatum(..),
  LoanRedeemer(..),
  CurrencySymbol(..),
  TokenName(..),
  POSIXTime(..),
  adaSymbol,
  adaToken,
  fromGHC,
  unsafeRatio,
  (-),(*),(+),
  loanValidatorCode
) where

import PlutusLedgerApi.V1.Value (valueOf)
import PlutusLedgerApi.V3
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

PlutusTx.unstableMakeIsData ''LoanDatum
PlutusTx.unstableMakeIsData ''LoanRedeemer


mkLoan :: LoanDatum -> LoanRedeemer -> ScriptContext -> Bool
mkLoan loanDatum r ctx = True
  where
    ScriptContext{scriptContextTxInfo=info} = ctx

    -- | Get the credential for this input as well as its value.
    -- Credential is used to check asset flux for address and ensure staking credential approves
    -- when necessary. The value is used to quickly check for beacon tokens.
    (inputCredentials,inputValue) =
      let TxOut{txOutAddress=addr,txOutValue=iVal} = ownInput ctx
      in (addr,iVal)

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

    -- | Checks that no collateral is taken during RepayLoan (unless loan fully paid off).
    noCollateralTaken :: Bool
    noCollateralTaken = trace "This string should not print" True
      -- FIXME uncommenting this code causes an evaluation error when running
      -- cabal run plutus-benchmark:cardano-loans
      -- let foo _ acc [] = acc
      --     foo val !acc ((collatAsset,_):xs) =
      --       foo val (acc && uncurry (valueOf val) collatAsset == 0) xs
      -- in foo addrDiff True (collateralRates loanDatum)

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
