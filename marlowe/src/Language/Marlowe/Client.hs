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

{-|
    Marlowe Mockchain client code.

    Below functions emulate executing Malrowe off-chain code on a client side.
    This implementation uses Plutus Mockchain, but it's expected to have quite similar API
    for the actual wallet implementation.
-}
module Language.Marlowe.Client where
import           Control.Applicative            ( Applicative(..) )
import           Control.Monad                  ( Monad(..)
                                                , void
                                                , when
                                                )
import           Control.Monad.Error.Class      ( MonadError(..) )
import           Data.Maybe                     ( maybeToList )
import qualified Data.Set                       as Set
import           Wallet                         ( WalletAPI(..)
                                                , WalletAPIError
                                                , intervalFrom
                                                , throwOtherError
                                                , createTxAndSubmit
                                                , ownPubKeyTxOut
                                                )
import           Ledger                         ( DataScript(..)
                                                , PubKey(..)
                                                , Slot(..)
                                                , Tx
                                                , TxOutRef
                                                , TxIn
                                                , TxOut
                                                , TxOutOf(..)
                                                , ValidatorScript(..)
                                                , scriptTxIn
                                                , scriptTxOut
                                                )
import qualified Ledger                         as Ledger
import           Ledger.Ada                  (Ada)
import qualified Ledger.Ada                     as Ada
import           Ledger.Validation
import           Language.Marlowe

{- Mockchain instantiation of Marlowe Interpreter functions. -}
eqValue :: Value -> Value -> Bool
eqValue = $$(equalValue)

eqObservation :: Observation -> Observation -> Bool
eqObservation = $$(equalObservation) eqValue

eqContract :: Contract -> Contract -> Bool
eqContract = $$(equalContract) eqValue eqObservation

validContract :: State -> Contract -> Slot -> Ada -> Bool
validContract = $$(validateContract)

evalValue :: Slot -> [OracleValue Integer] -> State -> Value -> Integer
evalValue pendingTxBlockHeight inputOracles = $$(evaluateValue) pendingTxBlockHeight inputOracles

interpretObs :: [OracleValue Integer] -> Integer -> State -> Observation -> Bool
interpretObs inputOracles blockNumber state obs = let
    ev = evalValue (Slot blockNumber) inputOracles
    in $$(interpretObservation) ev blockNumber state obs

evalContract :: PubKey -> TxHash -> Input -> Slot
    -> Ada -> Ada
    -> State -> Contract
    -> (State, Contract, Bool)
evalContract = $$(evaluateContract)

getScriptOutFromTx :: Tx -> (TxOut, TxOutRef)
getScriptOutFromTx = head . filter (Ledger.isPayToScriptOut . fst) . Ledger.txOutRefs

{-| Create Marlowe 'ValidatorScript' that remembers its owner.

    At the end of a contract execution owner can spend an initial deposit
    providing a 'Signature' for owner's public key.
 -}
marloweValidator :: PubKey -> ValidatorScript
marloweValidator creator = ValidatorScript result where
    result = Ledger.applyScript inner (Ledger.lifted creator)
    inner  = $$(Ledger.compileScript validatorScript)

{-| Create and submit a transaction that creates a Marlowe Contract @contract@
    using @validator@ script, and put @value@ Ada as a deposit.
-}
createContract :: (
    MonadError WalletAPIError m,
    WalletAPI m)
    => ValidatorScript
    -> Contract
    -> Integer
    -> m ()
createContract validator contract value = do
    _ <- if value <= 0 then throwOtherError "Must contribute a positive value" else pure ()
    slot <- slot
    let ds = DataScript $ Ledger.lifted (Input CreateContract [] [], MarloweData {
            marloweContract = contract,
            marloweState = emptyState })
    let v' = Ada.adaValueOf value
    (payment, change) <- createPaymentWithChange v'
    let o = scriptTxOut v' validator ds

    void $ createTxAndSubmit (intervalFrom slot) payment (o : maybeToList change)


{-| Prepare 'TxIn' and 'TxOut' generator for Marlowe style wallet actions.
-}
marloweTx ::
    (Input, MarloweData)
    -> (TxOut, TxOutRef)
    -- ^ reference to Marlowe contract UTxO
    -> ValidatorScript
    -- ^ actuall contract script
    -> (TxIn -> (Integer -> TxOut) -> Integer -> m ())
    -- ^ do wallet actions given Marlowe contract 'TxIn', contract 'TxOut' generator,
    --   and current contract money
    -> m ()
marloweTx inputState txOut validator f = let
    (TxOutOf _ vl _, ref) = txOut
    contractValue = Ada.toInt $ Ada.fromValue vl
    lifted = Ledger.lifted inputState
    scriptIn = scriptTxIn ref validator $ Ledger.RedeemerScript lifted
    dataScript = DataScript lifted
    scritOut v = scriptTxOut (Ada.adaValueOf v) validator dataScript
    in f scriptIn scritOut contractValue


-- | Create Marlowe Redeemer Script as @(Input, MarloweData)@.
createRedeemer
    :: InputCommand -> [OracleValue Integer] -> [Choice] -> State -> Contract -> (Input, MarloweData)
createRedeemer inputCommand oracles choices expectedState expectedCont =
    let input = Input inputCommand oracles choices
        mdata = MarloweData { marloweContract = expectedCont, marloweState = expectedState }
    in  (input, mdata)


{-| Create a Marlowe Commit input transaction given expected output 'Contract' and 'State'.
-}
commit :: (
    MonadError WalletAPIError m,
    WalletAPI m)
    => Tx
    -- ^ reference to Marlowe contract UTxO
    -> ValidatorScript
    -- ^ actuall contract script
    -> [OracleValue Integer]
    -- ^ Oracles values
    -> [Choice]
    -- ^ new 'Choice's
    -> IdentCC
    -- ^ commit identifier
    -> Integer
    -- ^ amount
    -> State
    -- ^ expected contract 'State' after commit
    -> Contract
    -- ^ expected 'Contract' after commit
    -> m ()
commit tx validator oracles choices identCC value expectedState expectedCont = do
    when (value <= 0) $ throwOtherError "Must commit a positive value"
    let (TxHash hash) = plcTxHash . Ledger.hashTx $ tx
    sig <- sign hash
    slot <- slot
    let redeemer = createRedeemer (Commit identCC sig) oracles choices expectedState expectedCont
    let txOut = getScriptOutFromTx tx
    marloweTx redeemer txOut validator $ \ contractTxIn getTxOut contractValue -> do
        (payment, change) <- createPaymentWithChange (Ada.adaValueOf value)
        void $ createTxAndSubmit
            (intervalFrom slot)
            (Set.insert contractTxIn payment)
            (getTxOut (contractValue + value) : maybeToList change)


{-| Create a Marlowe Commit input transaction given initial 'Contract' and its 'State'.

    Given current 'Contract' and its 'State' evaluate result 'Contract' and 'State.
    If resulting 'Contract' is valid then perform commit transaction.
-}
commit' :: (
    MonadError WalletAPIError m,
    WalletAPI m)
    => PubKey
    -- ^ contract creator
    -> Tx
    -- ^ reference to Marlowe contract UTxO
    -> ValidatorScript
    -- ^ actuall contract script
    -> [OracleValue Integer]
    -- ^ Oracles values
    -> [Choice]
    -- ^ new 'Choice's
    -> IdentCC
    -- ^ commit identifier
    -> Integer
    -- ^ amount
    -> State
    -- ^ contract 'State' before commit
    -> Contract
    -- ^ 'Contract' before commit
    -> m ()
commit' contractCreatorPK tx validator oracles choices identCC value inputState inputContract = do
    bh <- slot
    let txHash@(TxHash hash) = plcTxHash . Ledger.hashTx $ tx
    sig <- sign hash
    let inputCommand = Commit identCC sig
    let input = Input inputCommand oracles choices
    let txOut = getScriptOutFromTx tx
    let scriptInValue = Ada.fromValue . txOutValue . fst $ txOut
    let scriptOutValue = scriptInValue + Ada.fromInt value
    let (expectedState, expectedCont, isValid) =
            evalContract contractCreatorPK txHash
            input bh scriptInValue scriptOutValue inputState inputContract
    when (not isValid) $ throwOtherError "Invalid commit"
    commit tx validator oracles choices identCC value expectedState expectedCont


{-| Create a Marlowe Payment input transaction.
-}
receivePayment :: (
    MonadError WalletAPIError m,
    WalletAPI m)
    => Tx
    -- ^ reference to Marlowe contract UTxO
    -> ValidatorScript
    -- ^ actuall contract script
    -> [OracleValue Integer]
    -- ^ Oracles values
    -> [Choice]
    -- ^ new 'Choice's
    -> IdentPay
    -- ^ payment identifier
    -> Integer
    -- ^ amount
    -> State
    -- ^ expected contract 'State' after commit
    -> Contract
    -- ^ expected 'Contract' after commit
    -> m ()
receivePayment tx validator oracles choices identPay value expectedState expectedCont = do
    _ <- if value <= 0 then throwOtherError "Must commit a positive value" else pure ()
    let (TxHash hash) = plcTxHash . Ledger.hashTx $ tx
    sig <- sign hash
    slot <- slot
    let txOut = getScriptOutFromTx tx
    let redeemer = createRedeemer (Payment identPay sig) oracles choices expectedState expectedCont
    marloweTx redeemer txOut validator $ \ contractTxIn getTxOut contractValue -> do
        let out = getTxOut (contractValue - value)
        oo <- ownPubKeyTxOut (Ada.adaValueOf value)
        void $ createTxAndSubmit (intervalFrom slot) (Set.singleton contractTxIn) [out, oo]


{-| Create a Marlowe Redeem input transaction.
-}
redeem :: (
    MonadError WalletAPIError m,
    WalletAPI m)
    => Tx
    -- ^ reference to Marlowe contract UTxO
    -> ValidatorScript
    -- ^ actuall contract script
    -> [OracleValue Integer]
    -- ^ Oracles values
    -> [Choice]
    -- ^ new 'Choice's
    -> IdentCC
    -- ^ commit identifier
    -> Integer
    -- ^ amount to redeem
    -> State
    -- ^ expected contract 'State' after commit
    -> Contract
    -- ^ expected 'Contract' after commit
    -> m ()
redeem tx validator oracles choices identCC value expectedState expectedCont = do
    _ <- if value <= 0 then throwOtherError "Must commit a positive value" else pure ()
    let (TxHash hash) = plcTxHash . Ledger.hashTx $ tx
    sig <- sign hash
    slot <- slot
    let txOut = getScriptOutFromTx tx
    let redeemer = createRedeemer (Redeem identCC sig) oracles choices expectedState expectedCont
    marloweTx redeemer txOut validator $ \ contractTxIn getTxOut contractValue -> do
        let out = getTxOut (contractValue - value)
        oo <- ownPubKeyTxOut (Ada.adaValueOf value)
        void $ createTxAndSubmit (intervalFrom slot) (Set.singleton contractTxIn) [out, oo]


{-| Create a Marlowe SpendDeposit transaction.

    Spend the initial contract deposit payment.
-}
spendDeposit :: (Monad m, WalletAPI m)
    => Tx
    -- ^ reference to Marlowe contract UTxO
    -> ValidatorScript
    -- ^ actuall contract script
    -> State
    -- ^ current contract 'State'
    -> m ()
spendDeposit tx validator state = do
    let (TxHash hash) = plcTxHash . Ledger.hashTx $ tx
    sig <- sign hash
    slot <- slot
    let txOut = getScriptOutFromTx tx
    let redeemer = createRedeemer (SpendDeposit sig) [] [] state Null
    marloweTx redeemer txOut validator $ \ contractTxIn _ contractValue -> do
        oo <- ownPubKeyTxOut (Ada.adaValueOf contractValue)
        void $ createTxAndSubmit (intervalFrom slot) (Set.singleton contractTxIn) [oo]
