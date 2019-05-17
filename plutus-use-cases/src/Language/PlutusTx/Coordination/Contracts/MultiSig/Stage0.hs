{-# LANGUAGE DataKinds         #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell   #-}
{-# LANGUAGE TypeApplications  #-}
-- | Types and TH quotes for the multisig state machine contract.
module Language.PlutusTx.Coordination.Contracts.MultiSig.Stage0(
      Payment(..)
    , Params(..)
    , State(..)
    , Input(..)
    , step
    , stepWithChecks
    , stateEq
    ) where

import qualified Language.PlutusTx         as PlutusTx
import qualified Language.PlutusTx.Prelude as P
import           Ledger.Slot               (Slot)
import qualified Ledger.Slot               as Slot
import           Ledger.Validation         (PendingTx (..))
import qualified Ledger.Validation         as Validation
import           Ledger.Value              (Value)
import qualified Ledger.Value              as Value
import           Wallet

-- | A proposal for making a payment under the multisig scheme.
data Payment = Payment
    { paymentAmount    :: Value
    -- ^ How much to pay out
    , paymentRecipient :: PubKey
    -- ^ Address to pay the value to
    , paymentDeadline  :: Slot
    -- ^ Time until the required amount of signatures has to be collected.
    }

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
    InitialState Value
    -- ^ Money is locked, anyone can make a proposal for a payment-

    | CollectingSignatures Value Payment [PubKey]
    -- ^ A payment has been proposed and is awaiting signatures.

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

PlutusTx.makeLift ''Input

{-# INLINABLE isSignatory #-}
-- | Check if a public key is one of the signatories of the multisig contract.
isSignatory :: PubKey -> Params -> Bool
isSignatory pk (Params sigs _) = P.any (\pk' -> Validation.eqPubKey pk pk') sigs

{-# INLINABLE containsPk #-}
-- | Check whether a list of public keys contains a given key.
containsPk :: PubKey -> [PubKey] -> Bool
containsPk pk = P.any (\pk' -> Validation.eqPubKey pk' pk)

{-# INLINABLE pkListEq #-}
pkListEq :: [PubKey] -> [PubKey] -> Bool
pkListEq [] []           = True
pkListEq (k:ks) (k':ks') = P.and (Validation.eqPubKey k k') (pkListEq ks ks')
pkListEq _ _             = False

{-# INLINABLE isValidProposal #-}
-- | Check whether a proposed 'Payment' is valid given the total
--   amount of funds currently locked in the contract.
isValidProposal :: Value -> Payment -> Bool
isValidProposal vl (Payment amt _ _) = Value.leq amt vl

{-# INLINABLE proposalExpired #-}
-- | Check whether a proposed 'Payment' has expired.
proposalExpired :: PendingTx -> Payment -> Bool
proposalExpired (PendingTx _ _ _ _ _ rng _ _) (Payment _ _ ddl) = Slot.before ddl rng

{-# INLINABLE proposalAccepted #-}
-- | Check whether enough signatories (represented as a list of public keys)
--   have signed a proposed payment.
proposalAccepted :: Params -> [PubKey] -> Bool
proposalAccepted (Params signatories numReq) pks =
    let numSigned = P.length (P.filter (\pk -> containsPk pk pks) signatories)
    in P.geq numSigned numReq

{-# INLINABLE valuePreserved #-}
-- | @valuePreserved v p@ is true if the pending transaction @p@ pays the amount
--   @v@ to a single pay-to-script output at this script's address.
valuePreserved :: Value -> PendingTx -> Bool
valuePreserved vl ptx =
    let ownHash = Validation.ownHash ptx
        numOutputs = P.length (Validation.scriptOutputsAt ownHash ptx)
        valueLocked = Validation.valueLockedBy ptx ownHash
    in P.and (P.eq 1 numOutputs) (Value.eq valueLocked vl)

{-# INLINABLE valuePaid #-}
-- | @valuePaid pm ptx@ is true if the pending transaction @ptx@ pays
--   the amount specified in @pm@ to the public key address specified in @pm@
valuePaid :: Payment -> PendingTx -> Bool
valuePaid (Payment vl pk _) ptx = Value.eq vl (Validation.valuePaidTo ptx pk)

{-# INLINABLE paymentEq #-}
-- | Equality of 'Payment' values
paymentEq :: Payment -> Payment -> Bool
paymentEq (Payment vl pk sl) (Payment vl' pk' sl') =
    P.and (P.and (Value.eq vl vl') (Validation.eqPubKey pk pk')) (Slot.eq sl sl')

{-# INLINABLE stateEq #-}
-- | Equality of 'State' values
stateEq :: State -> State -> Bool
stateEq (InitialState v) (InitialState v') = Value.eq v v'
stateEq (CollectingSignatures vl pmt pks) (CollectingSignatures vl' pmt' pks') =
    P.and (P.and (Value.eq vl vl') (paymentEq pmt pmt')) (pkListEq pks pks')
stateEq _ _ = False

{-# INLINABLE step #-}
-- | @step params state input@ computes the next state given current state
--   @state@ and the input.
--   'step' does not perform any checks of the preconditions. This is done in
--   'stepWithChecks' below.
step :: State -> Input -> State
step =
    let step' :: State -> Input -> State
        step' s i =
            case (s, i) of
                (InitialState vl, ProposePayment pmt) ->
                    CollectingSignatures vl pmt []
                (CollectingSignatures vl pmt pks, AddSignature pk) ->
                    CollectingSignatures vl pmt (pk:pks)
                (CollectingSignatures vl _ _, Cancel) ->
                    InitialState vl
                (CollectingSignatures vl (Payment vp _ _) _, Pay) ->
                    let vl' = Value.minus vl vp in
                    InitialState vl'
                _ -> P.error (P.traceH "invalid transition" ())
    in step'

{-# INLINABLE stepWithChecks #-}
-- | @stepWithChecks params ptx state input@ computes the next state given
--   current state @state@ and the input. It checks whether the pending
--   transaction @ptx@ pays the expected amounts to script and public key
--   addresses. Fails with 'P.error' if an invalid transition is attempted.
stepWithChecks :: Params -> PendingTx -> State -> Input -> State
stepWithChecks =
    let step' :: Params -> PendingTx -> State -> Input -> State
        step' p ptx s i =
            let newState = step s i in
            case (s, i) of
                (InitialState vl, ProposePayment pmt) ->
                    if isValidProposal vl pmt `P.and`
                        valuePreserved vl ptx
                    then newState
                    else P.error (P.traceH "ProposePayment invalid" ())
                (CollectingSignatures vl _ pks, AddSignature pk) ->
                    if Validation.txSignedBy ptx pk `P.and`
                        isSignatory pk p `P.and`
                        P.not (containsPk pk pks) `P.and`
                        valuePreserved vl ptx
                    then newState
                    else P.error (P.traceH "AddSignature invalid" ())
                (CollectingSignatures vl pmt _, Cancel) ->
                    if proposalExpired ptx pmt `P.and`
                        valuePreserved vl ptx
                    then InitialState vl
                    else P.error (P.traceH "Cancel invalid" ())
                (CollectingSignatures vl pmt@(Payment vp _ _) pks, Pay) ->
                    let vl' = Value.minus vl vp in
                    if P.not (proposalExpired ptx pmt) `P.and`
                        proposalAccepted p pks `P.and`
                        valuePreserved vl' ptx `P.and`
                        valuePaid pmt ptx
                    then newState
                    else P.error (P.traceH "Pay invalid" ())
                _ -> P.error (P.traceH "invalid transition" ())
    in step'
