{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DefaultSignatures  #-}
{-# LANGUAGE DeriveAnyClass     #-}
{-# LANGUAGE DeriveGeneric      #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE RecordWildCards   #-}
{-# LANGUAGE RankNTypes   #-}
{-# LANGUAGE NamedFieldPuns   #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE TemplateHaskell   #-}
{-# OPTIONS_GHC -Wno-incomplete-uni-patterns -Wno-name-shadowing #-}
module Language.Marlowe.Client where
import           Control.Applicative            ( Applicative(..) )
import           Control.Monad                  ( Monad(..)
                                                , void
                                                , when
                                                )
import           Control.Monad.Error.Class      ( MonadError(..) )
import           Data.Maybe                     ( maybeToList )
import qualified Data.Set                       as Set
import qualified Language.PlutusTx              as PlutusTx
import           Wallet                         ( WalletAPI(..)
                                                , WalletAPIError
                                                , intervalFrom
                                                , throwOtherError
                                                , createTxAndSubmit
                                                , signature
                                                , ownPubKeyTxOut
                                                )
import           Ledger                         ( DataScript(..)
                                                , PubKey(..)
                                                , Signature(..)
                                                , Slot(..)
                                                , TxOutRef
                                                , TxIn
                                                , TxOut
                                                , TxOutOf(..)
                                                , ValidatorScript(..)
                                                , scriptTxIn
                                                , scriptTxOut
                                                )
import qualified Ledger                         as Ledger
import           Ledger.Validation
import           Language.Marlowe.Common

{- Mockchain instantiation of Marlowe Interpreter functions -}
eqValue :: Value -> Value -> Bool
eqValue = $$(equalValue)

eqObservation :: Observation -> Observation -> Bool
eqObservation = $$(equalObservation) eqValue

eqContract :: Contract -> Contract -> Bool
eqContract = $$(equalContract) eqValue eqObservation

validContract :: State -> Contract -> Slot -> Ledger.Value -> Bool
validContract = $$(validateContract)

evalValue :: Slot -> [OracleValue Int] -> State -> Value -> Int
evalValue pendingTxBlockHeight inputOracles = $$(evaluateValue) pendingTxBlockHeight inputOracles

interpretObs :: [OracleValue Int] -> Int -> State -> Observation -> Bool
interpretObs inputOracles blockNumber state obs = let
    ev = evalValue (Slot blockNumber) inputOracles
    in $$(interpretObservation) ev blockNumber state obs

evalContract :: PubKey -> Input -> Slot
    -> Ledger.Value -> Ledger.Value
    -> State -> Contract
    -> (State, Contract, Bool)
evalContract = $$(evaluateContract)


{-| Create Marlowe 'ValidatorScript' that remembers its owner.

    At the end of a contract execution owner can spend an initial deposit
    providing a 'Signature' for owner's public key.
 -}
marloweValidator :: PubKey -> ValidatorScript
marloweValidator creator = ValidatorScript result where
    result = Ledger.applyScript inner (Ledger.lifted creator)
    inner  = Ledger.fromCompiledCode $$(PlutusTx.compile [|| $$(validatorScript) ||])


{-| Create and submit a transaction that creates a Marlowe Contract @contract@
    using @validator@ script, and put @value@ Ada as a deposit.
-}
createContract :: (
    MonadError WalletAPIError m,
    WalletAPI m)
    => ValidatorScript
    -> Contract
    -> Int
    -> m ()
createContract validator contract value = do
    _ <- if value <= 0 then throwOtherError "Must contribute a positive value" else pure ()
    slot <- slot
    let ds = DataScript $ Ledger.lifted (Input (SpendDeposit (Signature 1)) [] [], MarloweData {
            marloweContract = contract,
            marloweState = emptyState })
    let v' = Ledger.Value value
    (payment, change) <- createPaymentWithChange v'
    let o = scriptTxOut v' validator ds

    void $ createTxAndSubmit (intervalFrom slot) payment (o : maybeToList change)


{-| Prepare 'TxIn' and 'TxOut' generator for Marlowe style wallet actions
-}
marloweTx ::
    (Input, MarloweData)
    -> (TxOut, TxOutRef)
    -> ValidatorScript
    -> (TxIn -> (Int -> TxOut) -> Int -> m ())
    -> m ()
marloweTx inputState txOut validator f = do
    let (TxOutOf _ (Ledger.Value contractValue) _, ref) = txOut
    let lifted = Ledger.lifted inputState
    let scriptIn = scriptTxIn ref validator $ Ledger.RedeemerScript lifted
    let dataScript = DataScript lifted
    let scritOut v = scriptTxOut (Ledger.Value v) validator dataScript
    f scriptIn scritOut contractValue


-- | Create Marlowe Redeemer Script as @(Input, MarloweData)@
createRedeemer
    :: InputCommand -> [OracleValue Int] -> [Choice] -> State -> Contract -> (Input, MarloweData)
createRedeemer inputCommand oracles choices expectedState expectedCont =
    let input = Input inputCommand oracles choices
        mdata = MarloweData { marloweContract = expectedCont, marloweState = expectedState }
    in  (input, mdata)


{-| Create a Marlowe Commit input transaction given expected output 'Contract' and 'State'
-}
commit' :: (
    MonadError WalletAPIError m,
    WalletAPI m)
    => (TxOut, TxOutRef)
    -> ValidatorScript
    -> [OracleValue Int]
    -> [Choice]
    -> IdentCC
    -> Int
    -> State
    -> Contract
    -> m ()
commit' txOut validator oracles choices identCC value expectedState expectedCont = do
    when (value <= 0) $ throwOtherError "Must commit a positive value"
    sig <- signature <$> myKeyPair
    slot <- slot
    let redeemer = createRedeemer (Commit identCC sig) oracles choices expectedState expectedCont
    marloweTx redeemer txOut validator $ \ contractTxIn getTxOut contractValue -> do
        (payment, change) <- createPaymentWithChange (Ledger.Value value)
        void $ createTxAndSubmit
            (intervalFrom slot)
            (Set.insert contractTxIn payment)
            (getTxOut (contractValue + value) : maybeToList change)


{-| Create a Marlowe Commit input transaction given initial 'Contract' and its 'State'
-}
commit :: (
    MonadError WalletAPIError m,
    WalletAPI m)
    => (TxOut, TxOutRef)
    -> ValidatorScript
    -> [OracleValue Int]
    -> [Choice]
    -> IdentCC
    -> Int
    -> State
    -> Contract
    -> m ()
commit txOut validator oracles choices identCC value inputState inputContract = do
    bh <- slot
    sig <- signature <$> myKeyPair
    let inputCommand = Commit identCC sig
    let input = Input inputCommand oracles choices
    let scriptInValue@(Ledger.Value contractValue) = txOutValue . fst $ txOut
    let scriptOutValue = Ledger.Value $ contractValue + value
    let (expectedState, expectedCont, isValid) =
            evalContract (PubKey 1) input bh scriptInValue scriptOutValue inputState inputContract
    when (not isValid) $ throwOtherError "Invalid commit"
    commit' txOut validator oracles choices identCC value expectedState expectedCont


{-| Create a Marlowe Payment input transaction
-}
receivePayment :: (
    MonadError WalletAPIError m,
    WalletAPI m)
    => (TxOut, TxOutRef)
    -> ValidatorScript
    -> [OracleValue Int]
    -> [Choice]
    -> IdentPay
    -> Int
    -> State
    -> Contract
    -> m ()
receivePayment txOut validator oracles choices identPay value expectedState expectedCont = do
    _ <- if value <= 0 then throwOtherError "Must commit a positive value" else pure ()
    sig <- signature <$> myKeyPair
    slot <- slot
    let redeemer = createRedeemer (Payment identPay sig) oracles choices expectedState expectedCont
    marloweTx redeemer txOut validator $ \ contractTxIn getTxOut contractValue -> do
        let out = getTxOut (contractValue - value)
        oo <- ownPubKeyTxOut (Ledger.Value value)
        void $ createTxAndSubmit (intervalFrom slot) (Set.singleton contractTxIn) [out, oo]


{-| Create a Marlowe Redeem input transaction
-}
redeem :: (
    MonadError WalletAPIError m,
    WalletAPI m)
    => (TxOut, TxOutRef)
    -> ValidatorScript
    -> [OracleValue Int]
    -> [Choice]
    -> IdentCC
    -> Int
    -> State
    -> Contract
    -> m ()
redeem txOut validator oracles choices identCC value expectedState expectedCont = do
    _ <- if value <= 0 then throwOtherError "Must commit a positive value" else pure ()
    sig <- signature <$> myKeyPair
    slot <- slot
    let redeemer = createRedeemer (Redeem identCC sig) oracles choices expectedState expectedCont
    marloweTx redeemer txOut validator $ \ contractTxIn getTxOut contractValue -> do
        let out = getTxOut (contractValue - value)
        oo <- ownPubKeyTxOut (Ledger.Value value)
        void $ createTxAndSubmit (intervalFrom slot) (Set.singleton contractTxIn) [out, oo]


{-| Create a Marlowe SpendDeposit transaction

    Spend the initial contract deposit payment.
-}
endContract :: (Monad m, WalletAPI m) => (TxOut, TxOutRef) -> ValidatorScript -> State -> m ()
endContract txOut validator state = do
    sig <- signature <$> myKeyPair
    slot <- slot
    let redeemer = createRedeemer (SpendDeposit sig) [] [] state Null
    marloweTx redeemer txOut validator $ \ contractTxIn _ contractValue -> do
        oo <- ownPubKeyTxOut (Ledger.Value contractValue)
        void $ createTxAndSubmit (intervalFrom slot) (Set.singleton contractTxIn) [oo]
