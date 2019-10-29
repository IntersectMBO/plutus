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
{-# OPTIONS_GHC -Wno-name-shadowing #-}
{-# OPTIONS_GHC -fno-ignore-interface-pragmas #-}
{-# OPTIONS_GHC -fno-omit-interface-pragmas #-}
{-# OPTIONS_GHC -fno-specialise #-}

module Language.Marlowe.Client where
import           Control.Monad              (Monad (..), void)
import           Control.Monad.Error.Class  (MonadError (..))
import           Data.Map                   (Map)
import qualified Data.Map                   as Map
import           Data.Maybe                 (maybeToList)
import qualified Data.Set                   as Set
import qualified Data.Text                  as Text
import           Language.Marlowe.Semantics as Marlowe
import qualified Language.PlutusTx          as PlutusTx
import           Ledger                     (DataScript (..), PubKey (..), Slot (..), Tx, TxOut, TxOutOf (..), interval,
                                             mkValidatorScript, pubKeyTxOut, scriptAddress, scriptTxIn, scriptTxOut,
                                             txOutRefs)
import           Ledger.Ada                 (Ada)
import qualified Ledger.Ada                 as Ada
import           Ledger.Scripts             (RedeemerScript (..), ValidatorScript)
import qualified Ledger.Typed.Scripts       as Scripts
import           Wallet                     (WalletAPI (..), WalletAPIError, createPaymentWithChange, createTxAndSubmit,
                                             throwOtherError)

{-| Create a Marlowe contract.
    Uses wallet public key to generate a unique script address.
 -}
createContract :: (
    MonadError WalletAPIError m,
    WalletAPI m)
    => Contract
    -> m MarloweData
createContract contract = do
    slot <- slot
    creator <- ownPubKey
    let validator = validatorScript creator

        marloweData = MarloweData {
            marloweCreator = creator,
            marloweContract = contract,
            marloweState = emptyState slot }
        ds = DataScript $ PlutusTx.toData marloweData

        deposit = Ada.adaValueOf 1

    (payment, change) <- createPaymentWithChange deposit
    let o = scriptTxOut deposit validator ds
        slotRange = interval slot (slot + 10)
        outputs = o : maybeToList change

    void $ createTxAndSubmit slotRange payment outputs
    return marloweData


{-| Deposit 'amount' of money to 'accountId' to a Marlowe contract
    from 'tx' with 'MarloweData' data script.
 -}
deposit :: (
    MonadError WalletAPIError m,
    WalletAPI m)
    => Tx
    -> MarloweData
    -> AccountId
    -> Ada
    -> m MarloweData
deposit tx marloweData accountId amount = do
    pubKey <- ownPubKey
    applyInputs tx marloweData [IDeposit accountId pubKey amount]


{-| Notify a contract -}
notify :: (
    MonadError WalletAPIError m,
    WalletAPI m)
    => Tx
    -> MarloweData
    -> m MarloweData
notify tx marloweData = applyInputs tx marloweData [INotify]


{-| Make a 'choice' identified as 'choiceId'. -}
makeChoice :: (
    MonadError WalletAPIError m,
    WalletAPI m)
    => Tx
    -> MarloweData
    -> ChoiceId
    -> Integer
    -> m MarloweData
makeChoice tx marloweData choiceId choice = applyInputs tx marloweData [IChoice choiceId choice]


{-| Create a simple transaction that just evaluates/reduces a contract.

    Imagine a contract:
    @
    If (SlotIntervalStart `ValueLT` (Constant 100))
        (When [] 200 (.. receive payment ..))
        Close
    @
    In order to receive a payment, one have to firts evaluate the contract
    before slot 100, and this transaction should not have any inputs.
    Then, after slot 200, one can evaluate again to claim the payment.
-}
makeProgress :: (
    MonadError WalletAPIError m,
    WalletAPI m)
    => Tx
    -> MarloweData
    -> m MarloweData
makeProgress tx marloweData = applyInputs tx marloweData []


{-| Apply a list of 'Input' to a Marlowe contract.
    All inputs must be from a wallet owner.
    One can only apply an input that's expected from his/her PubKey.
-}
applyInputs :: (
    MonadError WalletAPIError m,
    WalletAPI m)
    => Tx
    -> MarloweData
    -> [Input]
    -> m MarloweData
applyInputs tx MarloweData{..} inputs = do
    let depositAmount = Ada.adaOf 1
        depositPayment = Payment marloweCreator depositAmount
        redeemer = mkRedeemer inputs
        validator = validatorScript marloweCreator
        address = scriptAddress validator
    slot <- slot

    -- For now, we expect a transaction to happen whithin 10 slots from now.
    -- That's about 3 minutes, should be fine.
    let slotRange = interval slot (slot + Slot 10)
    let txInput = TransactionInput {
            txInterval = (slot, slot + Slot 10),
            txInputs = inputs }

    ref <- case filter (isAddress address) (txOutRefs tx) of
        [(_, ref)] -> pure ref
        [] -> throwOtherError ("Tx has no Marlowe contract of address "
            <> Text.pack (show address))
        _ -> throwOtherError ("Tx has multiple contracts of address "
            <> Text.pack (show address))

    let scriptIn = scriptTxIn ref validator redeemer
    let computedResult = computeTransaction txInput marloweState marloweContract

    (deducedTxOutputs, marloweData) <- case computedResult of
        TransactionOutput {txOutPayments, txOutState, txOutContract} -> do

            let marloweData = MarloweData {
                    marloweCreator,
                    marloweContract = txOutContract,
                    marloweState = txOutState }

            let deducedTxOutputs = case txOutContract of
                    Close -> txPaymentOuts (depositPayment : txOutPayments)
                    _ -> let
                        payouts = txPaymentOuts txOutPayments
                        totalPayouts = foldMap (Ada.fromValue . txOutValue) payouts
                        finalBalance = totalIncome - totalPayouts + depositAmount
                        dataScript = DataScript (PlutusTx.toData marloweData)
                        scriptOutValue = Ada.toValue finalBalance
                        scriptOut = scriptTxOut scriptOutValue validator dataScript
                        in scriptOut : payouts

            return (deducedTxOutputs, marloweData)
        Error txError -> throwOtherError (Text.pack $ show txError)


    (payment, change) <- if totalIncome > mempty
        then createPaymentWithChange (Ada.toValue totalIncome)
        else return (Set.empty, Nothing)

    void $ createTxAndSubmit
        slotRange
        (Set.insert scriptIn payment)
        (deducedTxOutputs ++ maybeToList change)

    return marloweData
  where
    collectDeposits (IDeposit _ _ money) = money
    collectDeposits _                    = mempty

    totalIncome = foldMap collectDeposits inputs

    isAddress address (TxOutOf{txOutAddress}, _) = txOutAddress == address

    txPaymentOuts :: [Payment] -> [TxOut]
    txPaymentOuts payments = let
        ps = foldr collectPayments Map.empty payments
        txOuts = [pubKeyTxOut (Ada.toValue value) pk | (pk, value) <- Map.toList ps]
        in txOuts

    collectPayments :: Payment -> Map Party Ada -> Map Party Ada
    collectPayments (Payment party money) payments = let
        newValue = case Map.lookup party payments of
            Just value -> value + money
            Nothing    -> money
        in Map.insert party newValue payments


{-| Generate a validator script for 'creator' PubKey -}
validatorScript :: PubKey -> ValidatorScript
validatorScript creator = mkValidatorScript ($$(PlutusTx.compile [|| validatorParam ||])
    `PlutusTx.applyCode`
        PlutusTx.liftCode creator)
    where validatorParam k = Scripts.wrapValidator (marloweValidator k)


{-| Make redeemer script -}
mkRedeemer :: [Input] -> RedeemerScript
mkRedeemer inputs = RedeemerScript (PlutusTx.toData inputs)
