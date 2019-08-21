[source,haskell]
----
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

{-# OPTIONS_GHC -fno-ignore-interface-pragmas #-}
{-# OPTIONS_GHC -fno-omit-interface-pragmas #-}

----
Below functions emulate executing Malrowe off-chain code on a client side.
This implementation uses Plutus Mockchain, but it's expected to have quite similar API
for the actual wallet implementation.

[source,haskell]
----

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
import qualified Ledger.Ada                     as Ada
import           Ledger.Validation
import           Language.Marlowe

{- Mockchain instantiation of Marlowe Interpreter functions. -}

interpretObs :: [OracleValue Integer] -> Integer -> State -> Observation -> Bool
interpretObs inputOracles blockNumber state obs = let
    ev = evaluateValue (Slot blockNumber) inputOracles
    in interpretObservation ev blockNumber state obs

getScriptOutFromTx :: Tx -> (TxOut, TxOutRef)
getScriptOutFromTx = head . filter (Ledger.isPayToScriptOut . fst) . Ledger.txOutRefs
----

The function `marloweValidator`, given the `PubKey` of the owner (and creator)
of a Marlowe contract, defines a validator. Note that his function is
universal in the sense that for every Marlowe contract, the _same_ validator
(modulo the creator's public key) is used, and the contract itself, as well
as its state, is found in the data script.  The public key is used in the
validation process.
Here we use the `validatorScript` function defined in the `Common` module.
At the end of a contract execution owner can spend an initial deposit
    providing a `Signature` for owner's public key.

[source,haskell]
----
marloweValidator :: PubKey -> ValidatorScript
marloweValidator creator = ValidatorScript result where
    result = Ledger.applyScript inner (Ledger.lifted creator)
    inner  = $$(Ledger.compileScript [|| validatorScript ||])
----

The `createContract` function is used by the wallet to create and submit a
transaction that puts a deposit of `value` locked by the given `validator` and
the data script `contract`, which is a Marlowe contract. Note that when
used, this function must be passed the Marlowe validator with the correct
public key. The initial input is the `CreateContract` command, and the
initial state is empty.

[source,haskell]
----
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
    let v' = Ada.lovelaceValueOf value
    (payment, change) <- createPaymentWithChange v'
    let o = scriptTxOut v' validator ds

    void $ createTxAndSubmit (intervalFrom slot) payment (o : maybeToList change)

----

Prepare 'TxIn' and 'TxOut' generator for Marlowe style wallet actions.
Explain more. A transaction that builds the set of TxIns and TxOuts.

[source,haskell]
----

marloweTx ::
    (Input, MarloweData)
    -- ^ redeemer is passed here
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
    contractValue = Ada.getLovelace $ Ada.fromValue vl
    lifted = Ledger.lifted inputState
    scriptIn = scriptTxIn ref validator $ Ledger.RedeemerScript lifted
    dataScript = DataScript lifted
    scritOut v = scriptTxOut (Ada.lovelaceValueOf v) validator dataScript
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
        (payment, change) <- createPaymentWithChange (Ada.lovelaceValueOf value)
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
    let scriptOutValue = scriptInValue + Ada.lovelaceOf value
    let (expectedState, expectedCont, isValid) =
            evaluateContract contractCreatorPK txHash
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
        oo <- ownPubKeyTxOut (Ada.lovelaceValueOf value)
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
        oo <- ownPubKeyTxOut (Ada.lovelaceValueOf value)
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
        oo <- ownPubKeyTxOut (Ada.lovelaceValueOf contractValue)
        void $ createTxAndSubmit (intervalFrom slot) (Set.singleton contractTxIn) [oo]
----
