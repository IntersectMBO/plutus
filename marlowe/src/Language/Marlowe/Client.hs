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
import           Control.Monad              (Monad (..))
import           Control.Monad.Error.Class  (MonadError (..))
import           Data.Map                   (Map)
import qualified Data.Map                   as Map
import           Data.Maybe                 (maybeToList)
import qualified Data.Set                   as Set
import qualified Data.Text                  as Text
import           Language.Marlowe.Semantics as Marlowe
import qualified Language.PlutusTx          as PlutusTx
import qualified Language.PlutusTx.Prelude  as P
import           Ledger                     (DataValue (..), PubKey (..), Slot (..), Tx, TxOut (..), interval,

                                             mkValidatorScript, pubKeyTxOut, scriptAddress, scriptTxIn, scriptTxOut,
                                             txOutRefs)
import           Ledger.Ada                 (adaValueOf)
import           Ledger.Scripts             (RedeemerValue (..), Validator)
import qualified Ledger.Typed.Scripts       as Scripts
import qualified Ledger.Value               as Val
import           Wallet                     (WalletAPI (..), WalletAPIError, createPaymentWithChange, createTxAndSubmit,
                                             throwOtherError)

{-| Create a Marlowe contract.
    Uses wallet public key to generate a unique script address.
 -}
createContract :: (
    MonadError WalletAPIError m,
    WalletAPI m)
    => Contract
    -> m (MarloweData, Tx)
createContract contract = do
    slot <- slot
    creator <- ownPubKey
    let validator = validatorScript creator

        marloweData = MarloweData {
            marloweCreator = creator,
            marloweContract = contract,
            marloweState = emptyState slot }
        ds = DataValue $ PlutusTx.toData marloweData

    let payValue = adaValueOf 1
    (payment, change) <- createPaymentWithChange payValue
    let o = scriptTxOut P.zero validator ds
        slotRange = interval slot (slot + 10)
        outputs = o : (pubKeyTxOut payValue creator) : maybeToList change

    tx <- createTxAndSubmit slotRange payment outputs [ds]
    return (marloweData, tx)


{-| Deposit 'amount' of 'token' to 'accountId' to a Marlowe contract
    from 'tx' with 'MarloweData' data script.
 -}
deposit :: (
    MonadError WalletAPIError m,
    WalletAPI m)
    => Tx
    -> MarloweData
    -> AccountId
    -> Token
    -> Integer
    -> m (MarloweData, Tx)
deposit tx marloweData accountId token amount = do
    pubKey <- ownPubKey
    applyInputs tx marloweData [IDeposit accountId pubKey token amount]


{-| Notify a contract -}
notify :: (
    MonadError WalletAPIError m,
    WalletAPI m)
    => Tx
    -> MarloweData
    -> m (MarloweData, Tx)
notify tx marloweData = applyInputs tx marloweData [INotify]


{-| Make a 'choice' identified as 'choiceId'. -}
makeChoice :: (
    MonadError WalletAPIError m,
    WalletAPI m)
    => Tx
    -> MarloweData
    -> ChoiceId
    -> Integer
    -> m (MarloweData, Tx)
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
    -> m (MarloweData, Tx)
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
    -> m (MarloweData, Tx)
applyInputs tx marloweData@MarloweData{..} inputs = do
    let redeemer = mkRedeemer inputs
        validator = validatorScript marloweCreator
        dataValue = DataValue (PlutusTx.toData marloweData)
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

    let scriptIn = scriptTxIn ref validator redeemer dataValue
    let computedResult = computeTransaction txInput marloweState marloweContract

    (deducedTxOutputs, marloweData) <- case computedResult of
        TransactionOutput {txOutPayments, txOutState, txOutContract} -> do

            let marloweData = MarloweData {
                    marloweCreator,
                    marloweContract = txOutContract,
                    marloweState = txOutState }

            let deducedTxOutputs = case txOutContract of
                    Close -> txPaymentOuts txOutPayments
                    _ -> let
                        payouts = txPaymentOuts txOutPayments
                        totalPayouts = foldMap txOutValue payouts
                        finalBalance = totalIncome P.- totalPayouts
                        dataValue = DataValue (PlutusTx.toData marloweData)
                        scriptOut = scriptTxOut finalBalance validator dataValue
                        in scriptOut : payouts

            return (deducedTxOutputs, marloweData)
        Error txError -> throwOtherError (Text.pack $ show txError)


    (payment, change) <- if totalIncome `Val.gt` P.zero
        then createPaymentWithChange totalIncome
        else return (Set.empty, Nothing)

    tx <- createTxAndSubmit
        slotRange
        (Set.insert scriptIn payment)
        (deducedTxOutputs ++ maybeToList change)
        [DataValue (PlutusTx.toData marloweData)]

    return (marloweData, tx)
  where
    collectDeposits (IDeposit _ _ (Token cur tok) amount) = Val.singleton cur tok amount
    collectDeposits _                    = P.zero

    totalIncome = foldMap collectDeposits inputs

    isAddress address (TxOut{txOutAddress}, _) = txOutAddress == address

    txPaymentOuts :: [Payment] -> [TxOut]
    txPaymentOuts payments = let
        ps = foldr collectPayments Map.empty payments
        txOuts = [pubKeyTxOut value pk | (pk, value) <- Map.toList ps]
        in txOuts

    collectPayments :: Payment -> Map Party Money -> Map Party Money
    collectPayments (Payment party money) payments = let
        newValue = case Map.lookup party payments of
            Just value -> value P.+ money
            Nothing    -> money
        in Map.insert party newValue payments


{-| Generate a validator script for 'creator' PubKey -}
validatorScript :: PubKey -> Validator
validatorScript creator = mkValidatorScript ($$(PlutusTx.compile [|| validatorParam ||])
    `PlutusTx.applyCode`
        PlutusTx.liftCode creator)
    where validatorParam k = Scripts.wrapValidator (marloweValidator k)


{-| Make redeemer script -}
mkRedeemer :: [Input] -> RedeemerValue
mkRedeemer inputs = RedeemerValue (PlutusTx.toData inputs)
