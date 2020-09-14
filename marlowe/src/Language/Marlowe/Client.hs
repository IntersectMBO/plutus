{-# LANGUAGE DataKinds          #-}
{-# LANGUAGE DefaultSignatures  #-}
{-# LANGUAGE DeriveAnyClass     #-}
{-# LANGUAGE DeriveGeneric      #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleContexts   #-}
{-# LANGUAGE MonoLocalBinds     #-}
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

import           Control.Monad.Freer
import           Control.Monad.Freer.Error  (Error)
import           Data.Map                   (Map)
import qualified Data.Map                   as Map
import           Data.Maybe                 (maybeToList)
import qualified Data.Set                   as Set
import qualified Data.Text                  as Text
import           Language.Marlowe.Semantics as Marlowe
import qualified Language.PlutusTx          as PlutusTx
import qualified Language.PlutusTx.Prelude  as P
import           Ledger                     (Address, CurrencySymbol, Datum (..), Slot (..), TokenName, Tx, interval,
                                             mkValidatorScript, pubKeyHash, pubKeyHashTxOut, scriptAddress, scriptTxIn,
                                             scriptTxOut, scriptTxOut', txOutRefs)
import           Ledger.Ada                 (adaSymbol, adaValueOf)
import           Ledger.Scripts             (Redeemer (..), Validator, validatorHash)
import qualified Ledger.Typed.Scripts       as Scripts
import           Ledger.Validation
import qualified Ledger.Value               as Val
import           Wallet                     (WalletAPIError, createPaymentWithChange, createTxAndSubmit, emptyPayment,
                                             throwOtherError)
import           Wallet.Effects             hiding (Payment)
import qualified Wallet.Effects             as Wallet

{-| Create a Marlowe contract.
    Uses wallet public key to generate a unique script address.
 -}
createContract :: (
    Member WalletEffect effs,
    Member SigningProcessEffect effs
    )
    => MarloweParams
    -> Contract
    -> Eff effs (MarloweData, Tx)
createContract params contract = do
    slot <- walletSlot
    creator <- pubKeyHash <$> ownPubKey
    let validator = validatorScript params

        marloweData = MarloweData {
            marloweContract = contract,
            marloweState = emptyState slot }
        ds = Datum $ PlutusTx.toData marloweData

    let payValue = adaValueOf 1
    Wallet.Payment{paymentInputs, paymentChangeOutput} <- createPaymentWithChange payValue
    let o = scriptTxOut P.zero validator ds
        slotRange = interval slot (slot + 10)
        outputs = o : (pubKeyHashTxOut payValue creator) : maybeToList paymentChangeOutput

    tx <- createTxAndSubmit slotRange paymentInputs outputs [ds]
    return (marloweData, tx)


{-| Deposit 'amount' of 'token' to 'accountId' to a Marlowe contract
    from 'tx' with 'MarloweData' data script.
 -}
deposit :: (
    Member WalletEffect effs,
    Member SigningProcessEffect effs,
    Member (Error WalletAPIError) effs
    )
    => Tx
    -> MarloweParams
    -> MarloweData
    -> AccountId
    -> Token
    -> Integer
    -> Eff effs (MarloweData, Tx)
deposit tx params marloweData accountId token amount = do
    pubKeyHash <- pubKeyHash <$> ownPubKey
    applyInputs tx params marloweData [IDeposit accountId (PK pubKeyHash) token amount]


{-| Notify a contract -}
notify :: (
    Member WalletEffect effs,
    Member SigningProcessEffect effs,
    Member (Error WalletAPIError) effs
    )
    => Tx
    -> MarloweParams
    -> MarloweData
    -> Eff effs (MarloweData, Tx)
notify tx params marloweData = applyInputs tx params marloweData [INotify]


{-| Make a 'choice' identified as 'choiceId'. -}
makeChoice :: (
    Member WalletEffect effs,
    Member SigningProcessEffect effs,
    Member (Error WalletAPIError) effs
    )
    => Tx
    -> MarloweParams
    -> MarloweData
    -> ChoiceId
    -> Integer
    -> Eff effs (MarloweData, Tx)
makeChoice tx params marloweData choiceId choice =
    applyInputs tx params marloweData [IChoice choiceId choice]


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
    Member WalletEffect effs,
    Member SigningProcessEffect effs,
    Member (Error WalletAPIError) effs
    )
    => Tx
    -> MarloweParams
    -> MarloweData
    -> Eff effs (MarloweData, Tx)
makeProgress tx params marloweData = applyInputs tx params marloweData []


{-| Apply a list of 'Input' to a Marlowe contract.
    All inputs must be from a wallet owner.
    One can only apply an input that's expected from his/her PubKey.
-}
applyInputs :: (
    Member WalletEffect effs,
    Member SigningProcessEffect effs,
    Member (Error WalletAPIError) effs
    )
    => Tx
    -> MarloweParams
    -> MarloweData
    -> [Input]
    -> Eff effs (MarloweData, Tx)
applyInputs tx params marloweData@MarloweData{..} inputs = do
    let redeemer = mkRedeemer inputs
        validator = validatorScript params
        dataValue = Datum (PlutusTx.toData marloweData)
        address = scriptAddress validator
    slot <- walletSlot

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

    ((deducedTxOutputs, dataValues), marloweData) <- case computedResult of
        TransactionOutput {txOutPayments, txOutState, txOutContract} -> do

            let marloweData = MarloweData {
                    marloweContract = txOutContract,
                    marloweState = txOutState }

            let deducedTxOutputsAndDataValues = case txOutContract of
                    Close -> txPaymentOuts txOutPayments
                    _ -> let
                        (payouts, dataValues) = txPaymentOuts txOutPayments
                        totalPayouts = foldMap txOutValue payouts
                        finalBalance = totalIncome P.- totalPayouts
                        dataValue = Datum (PlutusTx.toData marloweData)
                        scriptOut = scriptTxOut finalBalance validator dataValue
                        in (scriptOut : payouts, dataValue : dataValues)

            return (deducedTxOutputsAndDataValues, marloweData)
        Error txError -> throwOtherError (Text.pack $ show txError)


    Wallet.Payment{paymentInputs, paymentChangeOutput} <- if totalIncome `Val.gt` P.zero
        then createPaymentWithChange totalIncome
        else return Wallet.emptyPayment

    tx <- createTxAndSubmit
        slotRange
        (Set.insert scriptIn paymentInputs)
        (deducedTxOutputs ++ maybeToList paymentChangeOutput)
        dataValues

    return (marloweData, tx)
  where
    collectDeposits (IDeposit _ _ (Token cur tok) amount) = Val.singleton cur tok amount
    collectDeposits _                                     = P.zero

    totalIncome = foldMap collectDeposits inputs

    isAddress address (TxOut{txOutAddress}, _) = txOutAddress == address

    rolePayoutScriptAddress :: Address
    rolePayoutScriptAddress = scriptAddress rolePayoutScript

    txPaymentOuts :: [Payment] -> ([TxOut], [Datum])
    txPaymentOuts payments = foldMap paymentToTxOut paymentsByParty
      where
        paymentsByParty = Map.toList $ foldr collectPayments Map.empty payments

        paymentToTxOut (party, value) = case party of
            PK pk  -> ([pubKeyHashTxOut value pk], [])
            Role role -> let
                dataValue = Datum $ PlutusTx.toData (rolesCurrency params, role)
                txout = scriptTxOut' value rolePayoutScriptAddress dataValue
                in ([txout], [dataValue])

    collectPayments :: Payment -> Map Party Money -> Map Party Money
    collectPayments (Payment party money) payments = let
        newValue = money P.+ P.fromMaybe P.zero (Map.lookup party payments)
        in Map.insert party newValue payments


rolePayoutScript :: Validator
rolePayoutScript = mkValidatorScript ($$(PlutusTx.compile [|| wrapped ||]))
  where
    wrapped = Scripts.wrapValidator rolePayoutValidator


{-# INLINABLE rolePayoutValidator #-}
rolePayoutValidator :: (CurrencySymbol, TokenName) -> () -> ValidatorCtx -> Bool
rolePayoutValidator (currency, role) _ ctx =
    Val.valueOf (valueSpent (valCtxTxInfo ctx)) currency role P.> 0


marloweParams :: CurrencySymbol -> MarloweParams
marloweParams rolesCurrency = MarloweParams
    { rolesCurrency = rolesCurrency
    , rolePayoutValidatorHash = validatorHash rolePayoutScript }


defaultMarloweParams :: MarloweParams
defaultMarloweParams = marloweParams adaSymbol


{-| Generate a validator script for given Marlowe params -}
validatorScript :: MarloweParams -> Validator
validatorScript params = mkValidatorScript ($$(PlutusTx.compile [|| validatorParam ||])
    `PlutusTx.applyCode`
        PlutusTx.liftCode params)
  where
    validatorParam k = Scripts.wrapValidator (marloweValidator k)


{-| Make redeemer script -}
mkRedeemer :: [Input] -> Redeemer
mkRedeemer inputs = Redeemer (PlutusTx.toData inputs)
