{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE DataKinds       #-}
{-# LANGUAGE TemplateHaskell #-}
{-# OPTIONS_GHC -O0 #-}
-- | Implements a custom currency with a monetary policy that allows
--   the forging of a fixed amount of units.
module Language.PlutusTx.Coordination.Contracts.Currency(
      Currency(..)
    , curValidator
    -- * Actions etc
    , forge
    , forgedValue
    ) where

import           Control.Lens              ((^.), at, to)
import           Data.Bifunctor            (Bifunctor(first))
import qualified Data.Set                  as Set
import qualified Data.Map                  as Map
import           Data.Maybe                (fromMaybe)
import           Data.String               (IsString(fromString))
import qualified Data.Text                 as Text

import qualified Language.PlutusTx         as P

import qualified Ledger.Ada                as Ada
import qualified Ledger.Map                as LMap
import           Ledger.Scripts            (ValidatorScript(..))
import qualified Ledger.Validation         as V
import qualified Ledger.Value.TH           as Value
import           Ledger                    as Ledger hiding (to)
import           Ledger.Value              (Value)
import           Wallet.API                as WAPI

import qualified Language.PlutusTx.Coordination.Contracts.PubKey as PK
import           Language.PlutusTx.Coordination.Contracts.Currency.Stage0 as Stage0

mkCurrency :: TxOutRef -> [(String, Int)] -> Currency
mkCurrency (TxOutRefOf h i) amts = 
    Currency
        { curRefTransactionOutput = (V.plcTxHash h, i)
        , curAmounts              = LMap.fromList (fmap (first fromString) amts)
        }

curValidator :: Currency -> ValidatorScript
curValidator cur =
    ValidatorScript (Ledger.applyScript mkValidator (Ledger.lifted cur)) where
        mkValidator = Ledger.fromCompiledCode ($$(P.compile [||
            let validate :: Currency -> () -> () -> V.PendingTx -> ()
                validate c@(Currency (refHash, refIdx) _) () () p = 
                    let 
                        -- see note [Obtaining the currency symbol]
                        ownSymbol = $$(V.ownCurrencySymbol) p

                        forged = $$(V.valueForged) p
                        expected = $$currencyValue ownSymbol c
                            

                        -- True if the pending transaction forges the amount of
                        -- currency that we expect
                        forgeOK =
                            let v = $$(Value.eq) expected forged
                            in $$(P.traceIfFalseH) "Value forged different from expected" v

                        -- True if the pending transaction spends the output
                        -- identified by @(refHash, refIdx)@
                        txOutputSpent = 
                            let v = $$(V.spendsOutput) p refHash refIdx
                            in  $$(P.traceIfFalseH) "Pending transaction does not spend the designated transaction output" v

                    in
                        if $$(P.and) forgeOK txOutputSpent
                        then ()
                        else $$(P.error) ($$(P.traceH) "Invalid forge" ())
            in
                validate
            ||]))

{- note [Obtaining the currency symbol]

The currency symbol is the address (hash) of the validator. That is why
we can use 'Ledger.scriptAddress' here to get the symbol  in off-chain code, 
for example in 'forgedValue'.

Inside the validator script (on-chain) we can't use 'Ledger.scriptAddress',
because at that point we don't know the hash of the script yet. That
is why we use 'V.ownCurrencySymbol', which obtains the hash from the
'PendingTx' value.

-}

-- | The 'Value' forged by the 'curValidator' contract
forgedValue :: Currency -> Value
forgedValue cur = 
    let 
        -- see note [Obtaining the currency symbol]
        a = plcCurrencySymbol (Ledger.scriptAddress (curValidator cur))
    in
        $$currencyValue a cur

-- | @forge [(n1, c1), ..., (n_k, c_k)]@ creates a new currency with 
--   @k@ token names, forging @c_i@ units of each token @n_i@.
--   If @k == 0@ then no value is forged.
forge :: (WalletAPI m, WalletDiagnostics m) => [(String, Int)] -> m Currency
forge amounts = do
    pk <- WAPI.ownPubKey

    -- 1. We need to create the reference transaction output using the 
    --    'PublicKey' contract. That way we get an output that behaves
    --    like a normal public key output, but is not selected by the
    --    wallet during coin selection. This ensures that the output still 
    --    exists when we spend it in our forging transaction.
    (refAddr, refTxIn) <- PK.lock pk (Ada.adaValueOf 1)

    let

         -- With that we can define the currency
        theCurrency = mkCurrency (txInRef refTxIn) amounts
        curAddr     = Ledger.scriptAddress (curValidator theCurrency)
        forgedVal   = forgedValue theCurrency
        oneOrMore   = WAPI.intervalFrom $ Ada.adaValueOf 1

        -- trg1 fires when 'refTxIn' can be spent by our forging transaction
        trg1 = fundsAtAddressT refAddr oneOrMore
        
        -- trg2 fires when the pay-to-script output locked by 'curValidator' 
        -- is ready to be spent.
        trg2 = fundsAtAddressT curAddr oneOrMore

        -- The 'forge_' action creates a transaction that spends the contract
        -- output, forging the currency in the process.
        forge_ :: (WalletAPI m, WalletDiagnostics m) => m ()
        forge_ = do
            ownOutput <- WAPI.ownPubKeyTxOut (forgedVal <> Ada.adaValueOf 2)
            am <- WAPI.watchedAddresses

            let inputs' = am ^. at curAddr . to (Map.toList . fromMaybe Map.empty)
                con (r, _) = scriptTxIn r (curValidator theCurrency) (RedeemerScript $ Ledger.lifted ())
                ins        = con <$> inputs'

            let tx = Ledger.Tx
                        { txInputs = Set.fromList (refTxIn:ins)
                        , txOutputs = [ownOutput]
                        , txForge = forgedVal
                        , txFee   = Ada.zero
                        , txValidRange = defaultSlotRange
                        , txSignatures = Map.empty
                        }

            WAPI.logMsg $ Text.pack $ "Forging transaction: " <> show (Ledger.hashTx tx)
            WAPI.signTxAndSubmit_  tx

    -- 2. We start watching the contract address, ready to forge
    --    our currency once the monetary policy script has been
    --    placed on the chain.
    registerOnce trg2 (EventHandler $ const forge_)

    -- 3. When trg1 fires we submit a transaction that creates a 
    --    pay-to-script output locked by the monetary policy
    registerOnce trg1 (EventHandler $ const $ do
        payToScript_ defaultSlotRange curAddr (Ada.adaValueOf 1) (DataScript $ Ledger.lifted ()))

    -- Return the currency definition so that we can use the symbol
    -- in other places
    pure theCurrency
