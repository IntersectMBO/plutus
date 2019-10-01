{-# LANGUAGE TypeApplications  #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE TemplateHaskell   #-}
{-# LANGUAGE DataKinds         #-}
{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE NamedFieldPuns    #-}
{-# LANGUAGE ViewPatterns      #-}
{-# OPTIONS_GHC -fno-ignore-interface-pragmas #-}
{-# OPTIONS_GHC -fno-specialise #-}
{-# OPTIONS_GHC -fno-strictness #-}
-- | A multisig contract written as a state machine.
--   $multisig
module Language.PlutusTx.Coordination.Contracts.MultiSigStateMachine(
      Params(..)
    , Payment(..)
    , State
    , mkValidator
    , scriptInstance
    , initialise
    , lock
    , proposePayment
    , cancelPayment
    , addSignature
    , makePayment
    ) where

import           Data.Functor                 (void)
import           Control.Applicative          (Applicative (..))
import qualified Ledger.Interval              as Interval
import           Ledger.Validation            (PendingTx, PendingTx'(..))
import qualified Ledger.Validation            as Validation
import qualified Ledger.Typed.Tx              as Typed
import           Ledger.Value                 (Value)
import qualified Ledger.Value                 as Value
import           Wallet
import qualified Wallet                       as WAPI
import qualified Wallet.Typed.API             as WAPITyped

import qualified Language.PlutusTx            as PlutusTx
import qualified Language.PlutusTx.Applicative as PlutusTx
import           Language.PlutusTx.Prelude     hiding (check, Applicative (..))
import           Language.PlutusTx.StateMachine (StateMachine(..))
import qualified Language.PlutusTx.StateMachine as SM
import qualified Wallet.Typed.StateMachine as SM

--   $multisig
--   The n-out-of-m multisig contract works like a joint account of
--   m people, requiring the consent of n people for any payments.
--   In the smart contract the signatories are represented by public keys,
--   and approval takes the form of signatures on transactions.
--
--   The multisig contract in
--   'Language.PlutusTx.Coordination.Contracts.MultiSig' expects n signatures on
--   a single transaction. This requires an off-chain communication channel. The
--   multisig contract implemented in this module uses a proposal system that
--   allows participants to propose payments and attach their signatures to
--   proposals over a period of time, using separate transactions. All contract
--   state is kept on the chain so there is no need for off-chain communication.

-- | A proposal for making a payment under the multisig scheme.
data Payment = Payment
    { paymentAmount    :: Value
    -- ^ How much to pay out
    , paymentRecipient :: PubKey
    -- ^ Address to pay the value to
    , paymentDeadline  :: Slot
    -- ^ Time until the required amount of signatures has to be collected.
    }
    deriving (Show)

instance Eq Payment where
    {-# INLINABLE (==) #-}
    (Payment vl pk sl) == (Payment vl' pk' sl') = vl == vl' && pk == pk' && sl == sl'

instance PlutusTx.IsData Payment where
    {-# INLINABLE toData #-}
    toData (Payment amt key s) = PlutusTx.Constr 0 [PlutusTx.toData amt, PlutusTx.toData key, PlutusTx.toData s]
    {-# INLINABLE fromData #-}
    fromData (PlutusTx.Constr i [amt, key, s]) | i == 0 = Payment <$> PlutusTx.fromData amt PlutusTx.<*> PlutusTx.fromData key PlutusTx.<*> PlutusTx.fromData s
    fromData _ = Nothing

PlutusTx.makeLift ''Payment

data Params = Params
    { mspSignatories  :: [PubKey]
    -- ^ Public keys that are allowed to authorise payments
    , mspRequiredSigs :: Integer
    -- ^ How many signatures are required for a payment
    }

PlutusTx.makeLift ''Params

-- | State of the multisig contract.
data State =
    Holding Value
    -- ^ Money is locked, anyone can make a proposal for a payment. If there is
    -- no value here then this is a final state and the machine will terminate.

    | CollectingSignatures Value Payment [PubKey]
    -- ^ A payment has been proposed and is awaiting signatures.
    deriving (Show)

instance Eq State where
    {-# INLINABLE (==) #-}
    (Holding v) == (Holding v') = v == v'
    (CollectingSignatures vl pmt pks) == (CollectingSignatures vl' pmt' pks') =
        vl == vl' && pmt == pmt' && pks == pks'
    _ == _ = False

instance PlutusTx.IsData State where
    {-# INLINABLE toData #-}
    toData (Holding v) = PlutusTx.Constr 0 [PlutusTx.toData v]
    toData (CollectingSignatures v pm keys) = PlutusTx.Constr 1 [PlutusTx.toData v, PlutusTx.toData pm, PlutusTx.toData keys]
    {-# INLINABLE fromData #-}
    fromData (PlutusTx.Constr i [v]) | i == 0 = Holding <$> PlutusTx.fromData v
    fromData (PlutusTx.Constr i [v, pm, keys]) | i == 1 = CollectingSignatures <$> PlutusTx.fromData v PlutusTx.<*> PlutusTx.fromData pm PlutusTx.<*> PlutusTx.fromData keys
    fromData _ = Nothing

PlutusTx.makeLift ''State

data Input =
    ProposePayment Payment
    -- ^ Propose a payment. The payment can be made as soon as enough
    --   signatures have been collected.

    | AddSignature PubKey
    -- ^ Add a signature to the sigs. that have been collected for the
    --   current proposal.

    | Cancel
    -- ^ Cancel the current proposal if the deadline has passed

    | Pay
    -- ^ Make the payment.

instance PlutusTx.IsData Input where
    {-# INLINABLE toData #-}
    toData (ProposePayment pm) = PlutusTx.Constr 0 [PlutusTx.toData pm]
    toData (AddSignature key) = PlutusTx.Constr 1 [PlutusTx.toData key]
    toData (Cancel) = PlutusTx.Constr 2 []
    toData (Pay) = PlutusTx.Constr 3 []
    {-# INLINABLE fromData #-}
    fromData (PlutusTx.Constr i [pm]) | i == 0 = ProposePayment <$> PlutusTx.fromData pm
    fromData (PlutusTx.Constr i [key]) | i == 1 = AddSignature <$> PlutusTx.fromData key
    fromData (PlutusTx.Constr i []) | i == 2 = Just Cancel
    fromData (PlutusTx.Constr i []) | i == 3 = Just Pay
    fromData _ = Nothing

PlutusTx.makeLift ''Input


{-# INLINABLE isSignatory #-}
-- | Check if a public key is one of the signatories of the multisig contract.
isSignatory :: PubKey -> Params -> Bool
isSignatory pk (Params sigs _) = any (\pk' -> pk == pk') sigs

{-# INLINABLE containsPk #-}
-- | Check whether a list of public keys contains a given key.
containsPk :: PubKey -> [PubKey] -> Bool
containsPk pk = any (\pk' -> pk' == pk)

{-# INLINABLE isValidProposal #-}
-- | Check whether a proposed 'Payment' is valid given the total
--   amount of funds currently locked in the contract.
isValidProposal :: Value -> Payment -> Bool
isValidProposal vl (Payment amt _ _) = amt `Value.leq` vl

{-# INLINABLE proposalExpired #-}
-- | Check whether a proposed 'Payment' has expired.
proposalExpired :: PendingTx -> Payment -> Bool
proposalExpired PendingTx{pendingTxValidRange} Payment{paymentDeadline} =
    paymentDeadline `Interval.before` pendingTxValidRange

{-# INLINABLE proposalAccepted #-}
-- | Check whether enough signatories (represented as a list of public keys)
--   have signed a proposed payment.
proposalAccepted :: Params -> [PubKey] -> Bool
proposalAccepted (Params signatories numReq) pks =
    let numSigned = length (filter (\pk -> containsPk pk pks) signatories)
    in numSigned >= numReq

{-# INLINABLE valuePreserved #-}
-- | @valuePreserved v p@ is true if the pending transaction @p@ pays the amount
--   @v@ to this script's address. It does not assert the number of such outputs:
--   this is handled in the generic state machine validator.
valuePreserved :: Value -> PendingTx -> Bool
valuePreserved vl ptx = vl == Validation.valueLockedBy ptx (Validation.ownHash ptx)

{-# INLINABLE valuePaid #-}
-- | @valuePaid pm ptx@ is true if the pending transaction @ptx@ pays
--   the amount specified in @pm@ to the public key address specified in @pm@
valuePaid :: Payment -> PendingTx -> Bool
valuePaid (Payment vl pk _) ptx = vl == (Validation.valuePaidTo ptx pk)

{-# INLINABLE step #-}
-- | @step params state input@ computes the next state given current state
--   @state@ and the input.
--   'step' does not perform any checks of the preconditions. This is done in
--   'check' below.
step :: PlutusTx.Data -> PlutusTx.Data -> Maybe PlutusTx.Data
step (PlutusTx.fromData -> Just s) (PlutusTx.fromData -> Just i) = PlutusTx.toData <$> case (s, i) of
    (Holding vl, ProposePayment pmt) ->
        Just $ CollectingSignatures vl pmt []
    (CollectingSignatures vl pmt pks, AddSignature pk) ->
        Just $ CollectingSignatures vl pmt (pk:pks)
    (CollectingSignatures vl _ _, Cancel) ->
        Just $ Holding vl
    (CollectingSignatures vl (Payment vp _ _) _, Pay) ->
        let vl' = vl - vp in
        Just $ Holding vl'
    _ -> Nothing
step _ _ = Nothing

{-# INLINABLE check #-}
-- | @check params ptx state input@ checks whether the pending
--   transaction @ptx@ pays the expected amounts to script and public key
--   addresses.
check :: Params -> PlutusTx.Data -> PlutusTx.Data -> PendingTx -> Bool
check p (PlutusTx.fromData -> Just s) (PlutusTx.fromData -> Just i) ptx = case (s, i) of
    (Holding vl, ProposePayment pmt) ->
        isValidProposal vl pmt && valuePreserved vl ptx
    (CollectingSignatures vl _ pks, AddSignature pk) ->
        Validation.txSignedBy ptx pk &&
            isSignatory pk p &&
            not (containsPk pk pks) &&
            valuePreserved vl ptx
    (CollectingSignatures vl pmt _, Cancel) ->
        proposalExpired ptx pmt && valuePreserved vl ptx
    (CollectingSignatures vl pmt@(Payment vp _ _) pks, Pay) ->
        let vl' = vl - vp in
        not (proposalExpired ptx pmt) &&
            proposalAccepted p pks &&
            valuePreserved vl' ptx &&
            valuePaid pmt ptx
    _ -> False
check _ _ _ _ = False

{-# INLINABLE final #-}
-- | The machine is in a final state if we are holding no money.
final :: PlutusTx.Data -> Bool
final (PlutusTx.fromData -> Just (Holding v)) = Value.isZero v
final _ = False

{-# INLINABLE mkValidator #-}
mkValidator :: Params -> Typed.ValidatorType MultiSigSym
mkValidator p = SM.mkValidator $ StateMachine step (check p) final

validatorCode :: Params -> PlutusTx.CompiledCode (Typed.ValidatorType MultiSigSym)
validatorCode params = $$(PlutusTx.compile [|| mkValidator ||]) `PlutusTx.applyCode` PlutusTx.liftCode params

type MultiSigSym = StateMachine PlutusTx.Data PlutusTx.Data
scriptInstance :: Params -> Typed.ScriptInstance MultiSigSym
scriptInstance params = Typed.Validator $ validatorCode params

machineInstance :: Params -> SM.StateMachineInstance PlutusTx.Data PlutusTx.Data
machineInstance params =
    SM.StateMachineInstance
    (StateMachine step (check params) final)
    (scriptInstance params)
    stepRedeemerCode
    haltRedeemerCode

-- | Start watching the contract address
initialise :: WalletAPI m => Params -> m ()
initialise = WAPI.startWatching . Typed.scriptAddress . scriptInstance

-- | Lock some funds in a multisig contract.
lock
    :: (WalletAPI m, WalletDiagnostics m)
    => Params
    -- ^ Signatories and required signatures
    -> Value
    -- ^ The funds we want to lock
    -> m State
    -- ^ The initial state of the contract
lock prms vl = do
    (tx, state) <- SM.mkInitialise (machineInstance prms) (PlutusTx.toData $ Holding vl) vl

    void $ WAPITyped.signTxAndSubmit tx

    case PlutusTx.fromData state of
        Just s -> pure s
        Nothing -> WAPI.throwOtherError "Cannot decode state"

-- | Propose a payment from funds that are locked up in a state-machine based
--   multisig contract.
proposePayment
    :: (WalletAPI m, WalletDiagnostics m)
    => Params
    -> State
    -> Payment
    -> m State
proposePayment prms st = runStep prms st . ProposePayment

-- | Cancel a proposed payment
cancelPayment
    :: (WalletAPI m, WalletDiagnostics m)
    => Params
    -> State
    -> m State
cancelPayment prms st = runStep prms st Cancel

-- | Add a signature to a proposed payment
addSignature
    :: (WalletAPI m, WalletDiagnostics m)
    => Params
    -> State
    -> m State
addSignature prms st = WAPI.ownPubKey >>= runStep prms st . AddSignature

-- | Make a payment after enough signatures have been collected.
makePayment
    :: (WalletAPI m, WalletDiagnostics m)
    => Params
    -> State
    -> m State
makePayment prms currentState = do
    -- we can't use 'runStep' because the outputs of the transaction are
    -- different from the other transitions: We need two outputs, a public
    -- key output with the payment, and the script output with the remaining
    -- funds.
    (currentValue, valuePaid', recipient) <- case currentState of
        CollectingSignatures vl (Payment pd pk _) _ -> pure (vl, pd, pk)
        _ -> WAPI.throwOtherError "Cannot make payment because no payment has been proposed. Run the 'proposePayment' action first."
    let valueLeft = currentValue - valuePaid'
        -- Need to match to get the existential type out
        addOutAndPay (Typed.TypedTxSomeIns tx) = do
            let pkOut = Typed.makePubKeyTxOut valuePaid' recipient
                withPubKeyOut = tx { Typed.tyTxPubKeyTxOuts = [pkOut] }
            void $ WAPITyped.signTxAndSubmit withPubKeyOut

    st <- if Value.isZero valueLeft
          then do
              (scriptTx, newState) <- SM.mkHalt
                  (machineInstance prms)
                  (PlutusTx.toData currentState)
                  (PlutusTx.toData Pay)
              addOutAndPay scriptTx
              pure newState
          else do
              (scriptTx, newState) <- SM.mkStep
                  (machineInstance prms)
                  (PlutusTx.toData currentState)
                  (PlutusTx.toData Pay)
                  (const valueLeft)
              addOutAndPay scriptTx
              pure newState

    case PlutusTx.fromData st of
        Just s -> pure s
        Nothing -> WAPI.throwOtherError "Cannot decode state"

stepRedeemerCode :: PlutusTx.CompiledCode (PlutusTx.Data -> Typed.RedeemerFunctionType '[MultiSigSym] MultiSigSym)
stepRedeemerCode = $$(PlutusTx.compile [|| SM.mkStepRedeemer @PlutusTx.Data @PlutusTx.Data ||])

haltRedeemerCode :: PlutusTx.CompiledCode (PlutusTx.Data -> Typed.RedeemerFunctionType '[] MultiSigSym)
haltRedeemerCode = $$(PlutusTx.compile [|| SM.mkHaltRedeemer @PlutusTx.Data @PlutusTx.Data ||])

-- | Advance a running multisig contract. This applies the transition function
--   'SM.transition' to the current contract state and uses the result to unlock
--   the funds currently in the contract, and lock them again with a data script
--   containing the new state.
--
runStep
    :: (WalletAPI m, WalletDiagnostics m)
    => Params
    -- ^ The parameters of the contract instance
    -> State
    -- ^ Current state of the instance
    -> Input
    -- ^ Input to be applied to the contract
    -> m State
    -- ^ New state after applying the input
runStep prms currentState input = do
    (scriptTx, newState) <- SM.mkStep
        (machineInstance prms)
        (PlutusTx.toData currentState)
        (PlutusTx.toData input)
        id

    -- Need to match to get the existential type out
    case scriptTx of
        (Typed.TypedTxSomeIns tx) -> void $ WAPITyped.signTxAndSubmit tx

    case PlutusTx.fromData newState of
        Just s -> pure s
        Nothing -> WAPI.throwOtherError "Cannot decode state"

{- Note [Current state of the contract]

The 'mkStep' function takes the current state of the contract and returns the
new state. Both values are placed on the chain, so technically we don't have to
pass them around like this, but we currently can't decode 'State' values from
PLC back to Haskell.

-}
