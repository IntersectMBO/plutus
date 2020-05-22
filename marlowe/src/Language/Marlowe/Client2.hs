{-# LANGUAGE ConstraintKinds    #-}
{-# LANGUAGE DataKinds          #-}
{-# LANGUAGE DefaultSignatures  #-}
{-# LANGUAGE DeriveAnyClass     #-}
{-# LANGUAGE DeriveGeneric      #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleContexts   #-}
{-# LANGUAGE NamedFieldPuns     #-}
{-# LANGUAGE OverloadedStrings  #-}
{-# LANGUAGE RankNTypes         #-}
{-# LANGUAGE RecordWildCards    #-}
{-# LANGUAGE TemplateHaskell    #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeOperators       #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}
{-# OPTIONS_GHC -fno-ignore-interface-pragmas #-}
{-# OPTIONS_GHC -fno-omit-interface-pragmas #-}
{-# OPTIONS_GHC -fno-specialise #-}

module Language.Marlowe.Client2 where
import           Control.Monad              (Monad (..), void)
import           Control.Monad.Error.Class  (MonadError (..))
import           Control.Monad.Error.Lens   (throwing)
import           Control.Lens
import           Data.Map                   (Map)
import qualified Data.Map                   as Map
import           Data.Maybe                 (maybeToList)
import qualified Data.Set                   as Set
import qualified Data.Text                  as Text
import           Language.Plutus.Contract
import qualified Language.Plutus.Contract.Tx  as Tx
import           Language.Marlowe.Semantics hiding (Contract)
import qualified Language.Marlowe.Semantics as Marlowe
import qualified Language.PlutusTx          as PlutusTx
import qualified Language.PlutusTx.Prelude  as P
import           Ledger                     (PendingTx, CurrencySymbol, TokenName, Address(..),Datum (..), PubKeyHash (..), pubKeyHash, Slot (..), Tx, TxOut (..), TxOutRef(..), TxOutTx (..), interval,

                                             mkValidatorScript, pubKeyHashTxOut, scriptAddress, scriptTxIn, scriptTxOut, validatorHash, txOutDatum, txOutTxDatum,
                                             txOutRefs, scriptTxOut', valueSpent, pubKeyAddress)
import           Ledger.Ada                 (adaSymbol, adaValueOf)
import           Ledger.AddressMap                 (outRefMap)
import           Ledger.Scripts             (Redeemer (..), Validator)
import qualified Ledger.Typed.Scripts       as Scripts
import Ledger.Constraints
import qualified Ledger.Value               as Val
import Debug.Trace

type MarloweSchema =
    BlockchainActions
        .\/ Endpoint "create" (MarloweParams, Marlowe.Contract)
        .\/ Endpoint "apply-inputs" (MarloweParams, [Input])
        .\/ Endpoint "sub" MarloweParams


marloweContract2 :: forall e. (AsContractError e)
    => Contract MarloweSchema e ()
marloweContract2 = do
    create <|> apply {- <|> void sub -}
  where
    sub = do
        creator <- endpoint @"sub" @MarloweParams @MarloweSchema
        pk <- ownPubKey
        let validator = validatorScript creator
            address = Ledger.scriptAddress validator
        void $ utxoAt address
        utxoAt (pubKeyAddress pk)
    create = do
        (params, cont) <- endpoint @"create" @(MarloweParams, Marlowe.Contract) @MarloweSchema
        createContract params cont
    apply = do
        (params, inputs) <- endpoint @"apply-inputs" @(MarloweParams, [Input]) @MarloweSchema
        MarloweData{..} <- applyInputs params inputs
        case marloweContract of
            Close -> void apply --pure ()
            _ -> void apply


{-| Create a Marlowe contract.
    Uses wallet public key to generate a unique script address.
 -}
createContract :: (AsContractError e)
    => MarloweParams
    -> Marlowe.Contract
    -> Contract MarloweSchema e ()
createContract params contract = do
    slot <- awaitSlot 0
    creator <- pubKeyHash <$> ownPubKey
    let validator = validatorScript params
        vh = validatorHash validator

        marloweData = MarloweData {
            marloweContract = contract,
            marloweState = emptyState slot }
        ds = Datum $ PlutusTx.toData marloweData

    let payValue = adaValueOf 1

    let slotRange = interval slot (slot + 10)
    let tx = mustPayToOtherScript vh ds payValue
             <> mustValidateIn slotRange
    void $ submitTx tx


applyInputs :: (AsContractError e)
    => MarloweParams
    -> [Input]
    -> Contract MarloweSchema e MarloweData
applyInputs params inputs = do
    let redeemer = mkRedeemer inputs
        validator = validatorScript params
        address = scriptAddress validator
        vh = validatorHash validator
    traceM "Here"
    slot <- awaitSlot 0
    traceM "Here1"
    pk <- ownPubKey
    traceM "Here2"
    void $ utxoAt (pubKeyAddress pk)
    traceM "Here3"
    utxo <- utxoAt address
    traceM "Here4"
    let [(ref, out)] = Map.toList utxo


    let convert :: TxOutRef -> TxOutTx -> Maybe (TxOutRef, Val.Value, Datum, MarloweData)
        convert ref out = case (txOutTxDatum out) of
            Just dv -> case PlutusTx.fromData (getDatum dv) of
                Just marloweData -> Just (ref, txOutValue (txOutTxOut out), dv, marloweData)
                _ -> Nothing
            _ -> Nothing

    (ref, value, dataValue, MarloweData{..}) <- case convert ref out of
        Just r -> pure r
        Nothing -> throwing _OtherError $ (Text.pack $ "Not found")
    traceM "Here5"
    -- For now, we expect a transaction to happen whithin 10 slots from now.
    -- That's about 3 minutes, should be fine.
    let slotRange = interval slot (slot + Slot 10)
    let txInput = TransactionInput {
            txInterval = (slot, slot + Slot 10),
            txInputs = inputs }

    let computedResult = computeTransaction txInput marloweState marloweContract
    traceM "Here6"
    (tx, md) <- case computedResult of
        TransactionOutput {txOutPayments, txOutState, txOutContract} -> do

            let marloweData = MarloweData {
                    -- marloweCreator,
                    marloweContract = txOutContract,
                    marloweState = txOutState }

            let deducedTxOutputs = case txOutContract of
                    Close -> txPaymentOuts txOutPayments
                    _ -> let
                        txWithPayouts = txPaymentOuts txOutPayments
                        totalPayouts = foldMap (\(Payment _ v) -> v) txOutPayments
                        finalBalance = totalIncome P.- totalPayouts
                        dataValue = Datum (PlutusTx.toData marloweData)
                        scriptOut = mustPayToOtherScript vh dataValue finalBalance
                        in scriptOut <> txWithPayouts

            return (deducedTxOutputs, marloweData)
        Error txError -> throwing _OtherError $ (Text.pack $ show txError)
    traceM "Here7"
    let finalTx = tx <> mustSpendScriptOutput ref redeemer <> mustValidateIn slotRange
    -- traceM ("AAAAAAA" <> show finalTx)
    throwing _OtherError $ (Text.pack $ {- show finalTx -} "AAA" )
    void $ submitTx finalTx
    pure md
  where
    collectDeposits (IDeposit _ _ (Token cur tok) amount) = Val.singleton cur tok amount
    collectDeposits _                    = P.zero

    totalIncome = foldMap collectDeposits inputs

    isAddress address (TxOut{txOutAddress}, _) = txOutAddress == address

    -- txPaymentOuts :: [Payment] -> UnbalancedTx
    txPaymentOuts payments = foldMap paymentToTxOut paymentsByParty
      where
        paymentsByParty = Map.toList $ foldr collectPayments Map.empty payments

        paymentToTxOut (party, value) = case party of
            PK pk  -> mustPayToPubKey pk value
            Role role -> let
                dataValue = Datum $ PlutusTx.toData (rolesCurrency params, role)
                in mustPayToOtherScript (rolePayoutValidatorHash params) dataValue value




    collectPayments :: Payment -> Map Party Money -> Map Party Money
    collectPayments (Payment party money) payments = let
        newValue = money P.+ P.fromMaybe P.zero (Map.lookup party payments)
        in Map.insert party newValue payments

rolePayoutScript :: Validator
rolePayoutScript = mkValidatorScript ($$(PlutusTx.compile [|| wrapped ||]))
  where
    wrapped = Scripts.wrapValidator rolePayoutValidator


{-# INLINABLE rolePayoutValidator #-}
rolePayoutValidator :: (CurrencySymbol, TokenName) -> () -> PendingTx -> Bool
rolePayoutValidator (currency, role) _ pendingTx =
    Val.valueOf (valueSpent pendingTx) currency role P.> 0


marloweParams :: CurrencySymbol -> MarloweParams
marloweParams rolesCurrency = MarloweParams
    { rolesCurrency = rolesCurrency
    , rolePayoutValidatorHash = validatorHash rolePayoutScript }


defaultMarloweParams :: MarloweParams
defaultMarloweParams = marloweParams adaSymbol


{-| Generate a validator script for 'creator' PubKey -}
validatorScript :: MarloweParams -> Validator
validatorScript params = mkValidatorScript ($$(PlutusTx.compile [|| validatorParam ||])
    `PlutusTx.applyCode`
        PlutusTx.liftCode params)
  where
    validatorParam k = Scripts.wrapValidator (marloweValidator k)


{-| Make redeemer script -}
mkRedeemer :: [Input] -> Redeemer
mkRedeemer inputs = Redeemer (PlutusTx.toData inputs)
