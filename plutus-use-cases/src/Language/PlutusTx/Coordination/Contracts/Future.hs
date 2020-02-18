{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE MonoLocalBinds    #-}
{-# LANGUAGE ConstraintKinds   #-}
{-# LANGUAGE DataKinds         #-}
{-# LANGUAGE DeriveAnyClass    #-}
{-# LANGUAGE DeriveGeneric     #-}
{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE NamedFieldPuns    #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards   #-}
{-# LANGUAGE TemplateHaskell   #-}
{-# LANGUAGE TypeApplications  #-}
{-# LANGUAGE TypeOperators     #-}
{-# OPTIONS_GHC -fno-warn-unused-matches #-}
{-# OPTIONS_GHC -fno-warn-incomplete-uni-patterns #-}
{-# OPTIONS_GHC -fno-strictness #-}
{-# OPTIONS_GHC -fno-ignore-interface-pragmas #-}
{-# OPTIONS_GHC -fno-omit-interface-pragmas #-}
{-# OPTIONS -fplugin-opt Language.PlutusTx.Plugin:debug-context #-}
module Language.PlutusTx.Coordination.Contracts.Future(
    -- $future
      Future(..)
    , FutureAccounts(..)
    , mkAccounts
    , FutureError(..)
    , FutureSchema
    , FutureSetup(..)
    , Role(..)
    , futureContract
    , futureStateMachine
    , validator
    , initialiseFuture
    , initialMargin
    , futureAddress
    , tokenFor
    , initialState
    , scriptInstance
    , setupTokens
    ) where

import           Control.Lens                   (prism', review, makeClassyPrisms)
import           Control.Monad                  (void)
import           Control.Monad.Error.Lens       (throwing)
import           GHC.Generics                   (Generic)
import           Language.Plutus.Contract
import           Language.Plutus.Contract.Util  (loopM)
import qualified Language.PlutusTx              as PlutusTx
import           Language.PlutusTx.Prelude      hiding (Semigroup(..))
import qualified Language.PlutusTx.StateMachine as SM
import           Ledger                         (PubKey, pubKeyHash, Slot (..), Validator, Value, Address, DataValue(..), ValidatorHash)
import qualified Ledger
import qualified Ledger.Interval                as Interval
import           Ledger.Oracle                  (SignedMessage(..), Observation(..))
import qualified Ledger.Oracle                  as Oracle
import           Ledger.Tokens
import qualified Ledger.Typed.Scripts           as Scripts
import           Ledger.Validation              (PendingTx, PendingTx' (..))
import qualified Ledger.Validation              as Validation
import           Ledger.Value                   as Value

import qualified Language.PlutusTx.Coordination.Contracts.Currency as Currency
import Language.PlutusTx.Coordination.Contracts.Escrow (EscrowParams(..), AsEscrowError(..), EscrowError, RefundSuccess)
import qualified Language.PlutusTx.Coordination.Contracts.Escrow as Escrow
import qualified Language.PlutusTx.Coordination.Contracts.TokenAccount as TokenAccount
import Language.PlutusTx.Coordination.Contracts.TokenAccount (Account(..))
import           Language.Plutus.Contract.StateMachine (ValueAllocation(..), AsSMContractError, StateMachine(..))
import qualified Language.Plutus.Contract.StateMachine as SM

import qualified Prelude as Haskell
import           Prelude (Semigroup(..))

-- $future
-- A futures contract in Plutus. This example illustrates a number of concepts.
--   1. Maintaining a margin (a kind of deposit) during the duration of the contract to protect against breach of contract (see note [Futures in Plutus])
--   2. Using oracle values to obtain current pricing information (see note [Oracles] in Language.PlutusTx.Coordination.Contracts)
--   3. Writing contracts as state machines
--   4. Using tokens to represent claims on future cash flows

-- | Basic data of a futures contract. `Future` contains all values that do not
--   change during the lifetime of the contract.
--
data Future =
    Future
        { ftDeliveryDate  :: Slot
        , ftUnits         :: Integer
        , ftUnitPrice     :: Value
        , ftInitialMargin :: Value
        , ftPriceOracle   :: PubKey
        , ftMarginPenalty :: Value
        -- ^ How much a participant loses if they fail to make the required
        --   margin payments.
        } deriving Generic

-- | The two roles involved in the contract.
data Role = Long | Short
    deriving (Generic, Show)

instance Eq Role where
    Long == Long = True
    Short == Short = True
    _ == _ = False

-- | The token accounts that represent ownership of the two sides of the future.
--   When the contract is done, payments will be made to these accounts.
data FutureAccounts =
    FutureAccounts
        { ftoLong  :: Account
        -- ^ The owner of the "long" account (represented by a token)
        , ftoLongAccount :: ValidatorHash
        -- ^ Address of the 'TokenAccount' validator script for 'ftoLong'. This --   hash can be derived from 'ftoLong', but only in off-chain code. We
        --   store it here so that we can lift it into on-chain code.
        , ftoShort :: Account
        -- ^ The owner of the "short" account (represented by a token).
        , ftoShortAccount :: ValidatorHash
        -- ^ Address of the 'TokenAccount' validator script for 'ftoShort'. The
        --   comment on 'ftoLongAccount' applies to this as well.
        } deriving (Haskell.Show, Generic)

-- | The two margins.
data Margins =
    Margins
        { ftsShortMargin :: Value
        , ftsLongMargin  :: Value
        } deriving (Haskell.Eq, Show, Generic)

instance Eq Margins where
    l == r = ftsShortMargin l == ftsShortMargin r && ftsLongMargin l == ftsLongMargin r

-- | The state of the future contract.
data FutureState =
    Running Margins
    -- ^ Ongoing contract, with the current margins.
    | Finished
    -- ^ Contract is finished.
    deriving (Haskell.Eq, Show)

instance Eq FutureState where
    Running ma == Running ma' = ma == ma'
    Finished   == Finished    = True
    _ == _ = False

-- | Actions that can be performed on the future contract.
data FutureAction =
    AdjustMargin Role Value
    -- ^ Change the margin of one of the roles.
    | Settle (SignedMessage (Observation Value))
    -- ^ Close the contract at the delivery date by making the agreed payment
    --   and returning the margin deposits to their owners
    | SettleEarly (SignedMessage (Observation Value))
    -- ^ Close the contract early after a margin payment has been missed.
    --   The value of both margin accounts will be paid to the role that
    --   *didn't* violate the margin requirement
    deriving (Show)

data FutureError =
    TokenSetupFailed ContractError
    -- ^ Something went wrong during the setup of the two tokens
    | StateMachineError (SM.SMContractError FutureState FutureAction)
    | OtherFutureError ContractError
    | EscrowFailed EscrowError
    -- ^ The escrow that initialises the future contract failed
    | EscrowRefunded RefundSuccess
    -- ^ The other party didn't make their payment in time so the contract never
    --   started.
    deriving Show

makeClassyPrisms ''FutureError

instance AsSMContractError FutureError FutureState FutureAction where
    _SMContractError = _StateMachineError

instance AsContractError FutureError where
    _ContractError = _OtherFutureError

type FutureSchema =
    BlockchainActions
        .\/ Endpoint "initialise-future" (FutureSetup, Role)
        .\/ Endpoint "join-future" (FutureAccounts, FutureSetup)
        .\/ Endpoint "increase-margin" (Value, Role)
        .\/ Endpoint "settle-early" (SignedMessage (Observation Value))
        .\/ Endpoint "settle-future" (SignedMessage (Observation Value))

instance AsEscrowError FutureError where
    _EscrowError = prism' EscrowFailed (\case { EscrowFailed e -> Just e; _ -> Nothing})

futureContract :: Future -> Contract FutureSchema FutureError ()
futureContract ft = do
    client <- joinFuture ft <|> initialiseFuture ft
    void $ loopM (const $ selectEither (increaseMargin client) (settleFuture client <|> settleEarly client)) ()

-- | The data needed to initialise the futures contract.
data FutureSetup =
    FutureSetup
        { shortPK :: PubKey
        -- ^ Initial owner of the short token
        , longPK :: PubKey
        -- ^ Initial owner of the long token
        , contractStart :: Slot
        -- ^ Start of the futures contract itself. By this time the setup code
        --   has to be finished, otherwise the contract is void.
        } deriving (Haskell.Show)

{- note [Futures in Plutus]

A futures contract ("future") is an agreement to change ownership of an
asset at a certain time (the delivery time) for an agreed price (the forward
price). The time of the transfer, and the price, are fixed at the beginning of
the contract.

A future can be settled either by actually exchanging the asset for the price
(physical settlement) or by exchanging the difference between the forward price
and the spot (current) price.

In Plutus we could do physical settlement for assets that exist on the
blockchain, that is, for tokens and currencies (everything that's a 'Value'). But
the contract implemented here is for cash settlement.

The agreement involves two parties, a buyer (long position) and a seller (short
position). At the delivery time the actual price of the asset (spot price) is
quite likely different from the forward price. If the spot price is higher than
the forward price, then the seller transfers the difference to the buyer. If
the spot price is lower than the forward price, then the buyer transfers money
to the seller. In either case there is a risk that the payer does not meet their
obligation (by simply not paying). To protect against this risk, the contract
includes a kind of deposit called "margin".

Each party deposits an initial margin. If the price moves against the seller,
then the seller has to top up their margin periodically (in our case, once each
block). Likewise, if it moves against the buyer then the buyer has to top up
their margin. If either party fails to make a margin payment then the contract
will be settled early.

The current value of the underlying asset is determined by an oracle. See note
[Oracles] in Language.PlutusTx.Coordination.Contracts. Also note that we
wouldn't need oracles if this was a contract with physical settlement,

The contract has three phases: Initialisation, runtime, and settlement. In the
first phase both parties deposit their initial margins into an escrow contract.
The second phase is when the contract is "live". In this phase the contract
is a state machine whose state is the 'MarginnAccounts' with the current margins.
The transition from the second to the third phase happens either after the
settlement date, or if the sport price has moved so far that one of the margin
accounts is underfunded. The runtime and settlement phases are modeled as a state
machine, with 'FutureState' and 'FutureAction' types.

-}


mkAccounts
    :: Account
    -> Account
    -> FutureAccounts
mkAccounts long short =
    FutureAccounts
        { ftoLong = long
        , ftoLongAccount = TokenAccount.validatorHash long
        , ftoShort = short
        , ftoShortAccount = TokenAccount.validatorHash short
        }

{-# INLINABLE tokenFor #-}
tokenFor :: Role -> FutureAccounts -> Value
tokenFor = \case
    Long -> \case FutureAccounts{ftoLong=Account(sym,tn)} -> token sym tn
    Short -> \case FutureAccounts{ftoShort=Account(sym,tn)} -> token sym tn

{-# INLINABLE adjustMargin #-}
-- | Change the margin account of the role by the given amount.
adjustMargin :: Role -> Value -> Margins -> Margins
adjustMargin role value accounts =
    case role of
        Long  -> accounts { ftsLongMargin = ftsLongMargin accounts + value }
        Short -> accounts { ftsShortMargin = ftsShortMargin accounts + value }

{-# INLINABLE totalMargin #-}
-- | The combined value of both margin accounts.
totalMargin :: Margins -> Value
totalMargin Margins{ftsShortMargin, ftsLongMargin} =
    ftsShortMargin + ftsLongMargin

{-# INLINABLE futureStateMachine #-}
futureStateMachine
    :: Future
    -> FutureAccounts
    -> StateMachine FutureState FutureAction
futureStateMachine ft fos =
    StateMachine
        { smTransition = futureTransition
        , smCheck      = futureCheck ft fos
        , smFinal      = \case { Finished -> True; _ -> False }
        }

scriptInstance :: Future -> FutureAccounts -> Scripts.ScriptInstance (SM.StateMachine FutureState FutureAction)
scriptInstance future ftos =
    let val = $$(PlutusTx.compile [|| validatorParam ||])
            `PlutusTx.applyCode`
                PlutusTx.liftCode future
                `PlutusTx.applyCode`
                    PlutusTx.liftCode ftos
        validatorParam f g = SM.mkValidator (futureStateMachine f g)
        wrap = Scripts.wrapValidator @FutureState @FutureAction

    in Scripts.validator @(SM.StateMachine FutureState FutureAction)
        val
        $$(PlutusTx.compile [|| wrap ||])

machineClient
    :: Scripts.ScriptInstance (SM.StateMachine FutureState FutureAction)
    -> Future
    -> FutureAccounts
    -> SM.StateMachineClient FutureState FutureAction
machineClient inst future ftos =
    let machine = futureStateMachine future ftos
        i = SM.StateMachineInstance machine inst
    in SM.mkStateMachineClient i (allocate future ftos)

validator :: Future -> FutureAccounts -> Validator
validator ft fos = Scripts.validatorScript (scriptInstance ft fos)

{-# INLINABLE verifyOracleOnChain #-}
verifyOracleOnChain :: PlutusTx.IsData a => PendingTx -> Future -> SignedMessage (Observation a) -> Maybe (Slot, a)
verifyOracleOnChain ptx Future{ftPriceOracle} sm =
    case Oracle.verifySignedMessageOnChain ptx ftPriceOracle sm of
        Left _ -> Nothing
        Right Observation{obsValue, obsSlot} -> Just (obsSlot, obsValue)

verifyOracleOffChain :: PlutusTx.IsData a => Future -> SignedMessage (Observation a) -> Maybe (Slot, a)
verifyOracleOffChain Future{ftPriceOracle} sm =
    case Oracle.verifySignedMessageOffChain ftPriceOracle sm of
        Left _ -> Nothing
        Right Observation{obsValue, obsSlot} -> Just (obsSlot, obsValue)

{-# INLINABLE futureTransition #-}
futureTransition :: FutureState -> FutureAction -> Maybe FutureState
futureTransition (Running accounts) (AdjustMargin role value) = Just (Running (adjustMargin role value accounts))
futureTransition Running{} Settle{}      = Just Finished
futureTransition Running{} SettleEarly{} = Just Finished
futureTransition _ _                     = Nothing

data Payouts =
    Payouts
        { payoutsShort :: Value
        , payoutsLong  :: Value
        }

payoutsTx
    :: Payouts
    -> FutureAccounts
    -> UnbalancedTx
payoutsTx
    Payouts{payoutsShort, payoutsLong}
    FutureAccounts{ftoShort, ftoLong} =
        TokenAccount.payTx (TokenAccount.scriptInstance ftoShort) payoutsShort
        <> TokenAccount.payTx (TokenAccount.scriptInstance ftoLong) payoutsLong

{-# INLINABLE payouts #-}
-- | Compute the payouts for each role given the future data,
--   margin accounts, and current (spot) price
payouts :: Future -> Margins -> Value -> Payouts
payouts Future{ftUnits, ftUnitPrice} Margins{ftsShortMargin, ftsLongMargin} spotPrice =
    let delta = scale ftUnits (spotPrice - ftUnitPrice)
    in Payouts
        { payoutsShort = ftsShortMargin - delta
        , payoutsLong  = ftsLongMargin + delta
        }

{-# INLINABLE futureCheck #-}
futureCheck :: Future -> FutureAccounts -> FutureState -> FutureAction -> PendingTx -> Bool
futureCheck future owners state action ptx =
    let
        (ownHash, _, _) = Validation.ownHashes ptx
        vl = Validation.valueLockedBy ptx ownHash
    in
    case (state, action) of
        (Running accounts, AdjustMargin _ topUp) ->
                vl == (topUp + totalMargin accounts)
        (Running accounts, SettleEarly ov) ->
            let
                Future{ftDeliveryDate} = future
                FutureAccounts{ftoLongAccount, ftoShortAccount} = owners
                Just (oracleDate, spotPrice) = verifyOracleOnChain ptx future ov
                err = traceH "Margin requirements not violated" (error ())
                vRole = fromMaybe err (violatingRole future accounts spotPrice)
                payoutValid = case vRole of
                        Short -> Validation.valueLockedBy ptx ftoLongAccount `geq` totalMargin accounts
                        Long  -> Validation.valueLockedBy ptx ftoShortAccount `geq` totalMargin accounts
                slotValid = oracleDate < ftDeliveryDate
            in payoutValid && slotValid
        (Running accounts, Settle ov) ->
            let
                Future{ftDeliveryDate} = future
                FutureAccounts{ftoLongAccount, ftoShortAccount} = owners
                Just (oracleDate, spotPrice) = verifyOracleOnChain ptx future ov
                Payouts{payoutsShort, payoutsLong} = payouts future accounts spotPrice
                payoutValid =
                    Validation.valueLockedBy ptx ftoLongAccount `geq` payoutsLong
                    && Validation.valueLockedBy ptx ftoShortAccount `geq` payoutsShort
                slotvalid   = oracleDate == ftDeliveryDate
                                && ftDeliveryDate `Interval.before` pendingTxValidRange ptx
            in slotvalid && payoutValid
        _ -> False

allocate :: Future -> FutureAccounts -> FutureState -> FutureAction -> Value -> Maybe ValueAllocation
allocate _ _ Running{} (AdjustMargin _ topUp) vl =
    Just $ ValueAllocation
        { vaOwnAddress = topUp + vl
        , vaOtherPayments=Haskell.mempty
        }
allocate future ftos (Running margins) (SettleEarly ov) vl = do
    (_, spotPrice) <- verifyOracleOffChain future ov
    rl <- violatingRole future margins vl
    let Margins{ftsShortMargin, ftsLongMargin} = margins
        payments  =
            case rl of
                Long -> Payouts{payoutsLong=mempty, payoutsShort = ftsShortMargin + ftsLongMargin }
                Short -> Payouts{payoutsLong=ftsShortMargin+ftsLongMargin, payoutsShort = mempty}
    Just $ ValueAllocation
        { vaOwnAddress = mempty
        , vaOtherPayments = payoutsTx payments ftos <> mustIncludeDataValue (osmData ov)
        }
allocate future ftos (Running accounts) (Settle ov) vl = do
    (_, spotPrice) <- verifyOracleOffChain future ov
    let payments = payouts future accounts spotPrice
    Just $ ValueAllocation
        { vaOwnAddress = mempty
        , vaOtherPayments =
            payoutsTx payments ftos
                <> mustBeValidIn (Interval.from (succ $ ftDeliveryDate future))
                <> mustIncludeDataValue (osmData ov)
        }
allocate _ _ _ _ vl = Nothing

-- | Compute the required margin from the current price of the
--   underlying asset.
{-# INLINABLE requiredMargin #-}
requiredMargin :: Future -> Value -> Value
requiredMargin Future{ftUnits, ftUnitPrice, ftMarginPenalty} spotPrice =
    let
        delta  = scale ftUnits (spotPrice - ftUnitPrice)
    in
        ftMarginPenalty + delta

{-# INLINABLE initialMargin #-}
initialMargin :: Future -> Value
initialMargin ft@Future{ftUnitPrice, ftMarginPenalty} =
    ftMarginPenalty + ftUnitPrice

{-# INLINABLE initialState #-}
-- | The initial state of the 'Future' contract
initialState :: Future -> FutureState
initialState ft =
    let im = initialMargin ft in
    Running (Margins{ftsShortMargin=im, ftsLongMargin=im})

futureAddress :: Future -> FutureAccounts -> Address
futureAddress ft fo = Ledger.scriptAddress (validator ft fo)

{-# INLINABLE violatingRole #-}
-- | The role that violated its margin requirements
violatingRole :: Future -> Margins -> Value -> Maybe Role
violatingRole future margins spotPrice =
    let
        minMargin = requiredMargin future spotPrice
        Margins{ftsShortMargin, ftsLongMargin} = margins
    in
    if ftsShortMargin `lt` minMargin then Just Short
    else if ftsLongMargin `lt` minMargin then Just Long
    else Nothing

-- | Initialise the contract by
--   * Generating the tokens for long and short
--   * Setting up an escrow contract for the initial margins
--   * Paying the initial margin for the given role
initialiseFuture
    :: ( HasEndpoint "initialise-future" (FutureSetup, Role) s
       , HasBlockchainActions s
       , AsFutureError e
       )
    => Future
    -> Contract s e (SM.StateMachineClient FutureState FutureAction)
initialiseFuture future = do
    (s, ownRole) <- endpoint @"initialise-future" @(FutureSetup, Role)
    -- Start by setting up the two tokens for the short and long positions.
    ftos <- setupTokens

    -- Now we have a 'FutureAccountsValue' with the data of two new and unique
    -- tokens that we will use for the future contract. Now we use an escrow
    --  contract to initialise the future contract.

    inst <- checkpoint $ pure (scriptInstance future ftos)

    let
        client = machineClient inst future ftos

        -- The escrow parameters 'esc' ensure that the initial margin is paid
        -- to the future contract address, and the two tokens are transferred
        -- to their initial owners.
        escr = escrowParams client future ftos s

        -- For the escrow to go through, both tokens and 2x the initial margin
        -- have to be deposited at the escrow address before the deadline
        -- (start of the future contract). Since we are currently in possession
        -- of both tokens, we pay the two tokens and our own initial margin to
        -- the escrow.
        payment =
            initialMargin future <> tokenFor Long ftos <> tokenFor Short ftos

        -- By using 'Escrow.payRedeemRefund' we make our payment and wait for
        -- the other party to make theirs. If they fail to do so within the
        -- agreed timeframe, our own initial margin is refunded and the future
        -- contract never starts.
        escrowPayment = Escrow.payRedeemRefund escr payment

    -- Run 'escrowPayment', wrapping any errors in 'EscrowFailed'. If the escrow
    -- contract ended with a refund (ie., 'escrowPayment' returns a 'Left') we
    -- throw an 'EscrowRefunded' error. If the escrow contract succeeded, the
    -- future is initialised and ready to go, so we return the 'FutureAccounts'
    -- with the token information.
    e <- withContractError (review _EscrowFailed) escrowPayment
    either (throwing _EscrowRefunded) (\_ -> pure client) e

-- | The @"settle-future"@ endpoint. Given an oracle value with the current spot
--   price, this endpoint creates the final transaction that distributes the
--   funds locked by the future to the token accounts specified in
--   the 'FutureAccounts' argument.
settleFuture
    :: ( HasEndpoint "settle-future" (SignedMessage (Observation Value)) s
       , HasBlockchainActions s
       , AsSMContractError e FutureState FutureAction
       , AsContractError e
       )
    => SM.StateMachineClient FutureState FutureAction
    -> Contract s e ()
settleFuture client = do
    ov <- endpoint @"settle-future"
    void $ SM.runStep client (Settle ov)

-- | The @"settle-early"@ endpoint. Given an oracle value with the current spot
--   price, this endpoint creates the final transaction that distributes the
--   funds locked by the future to the token account of the role that did not
--   violate its obligations. Throws a 'MarginRequirementsNotViolated' error if
--   the spot price is within the margin range.
settleEarly
    :: ( HasEndpoint "settle-early" (SignedMessage (Observation Value)) s
       , HasBlockchainActions s
       , AsSMContractError e FutureState FutureAction
       , AsContractError e
       )
    => SM.StateMachineClient FutureState FutureAction
    -> Contract s e ()
settleEarly client = do
    ov <- endpoint @"settle-early"
    void $ SM.runStep client (SettleEarly ov)

-- | The @"increase-margin"@ endpoint. Increses the margin of one of
--   the roles by an amount.
increaseMargin
    :: ( HasEndpoint "increase-margin" (Value, Role) s
       , HasUtxoAt s
       , HasWriteTx s
       , HasTxConfirmation s
       , AsSMContractError e FutureState FutureAction
       , AsContractError e
       )
    => SM.StateMachineClient FutureState FutureAction
    -> Contract s e ()
increaseMargin client = do
    (value, role) <- endpoint @"increase-margin"
    void $ SM.runStep client (AdjustMargin role value)

-- | The @"join-future"@ endpoint. Join a future contract by paying the initial
--   margin to the escrow that initialises the contract.
joinFuture
    :: ( HasEndpoint "join-future" (FutureAccounts, FutureSetup) s
       , HasBlockchainActions s
       , AsFutureError e
       )
    => Future
    -> Contract s e (SM.StateMachineClient FutureState FutureAction)
joinFuture ft = do
    (owners, stp) <- endpoint @"join-future" @(FutureAccounts, FutureSetup)
    inst <- checkpoint $ pure (scriptInstance ft owners)
    let client = machineClient inst ft owners
        escr = escrowParams client ft owners stp
        payment = Escrow.pay (Escrow.scriptInstance escr) escr (initialMargin ft)
    void (withContractError (review _EscrowFailed) payment)
    pure client

-- | Create two unique tokens that can be used for the short and long positions
--   and return a 'FutureAccounts' value for them.
--
--   Note that after 'setupTokens' is complete, both tokens will be locked by a
--   public key output belonging to the wallet that ran 'setupTokens'.
setupTokens
    :: ( HasWriteTx s
       , HasWatchAddress s
       , HasOwnPubKey s
       , AsFutureError e
       )
    => Contract s e FutureAccounts
setupTokens = do
    pk <- ownPubKey

    -- Create the tokens using the currency contract, wrapping any errors in
    -- 'TokenSetupFailed'
    cur <- withContractError (review _TokenSetupFailed) (Currency.forgeContract (pubKeyHash pk) [("long", 1), ("short", 1)])
    let sym = Currency.currencySymbol cur
    pure $ mkAccounts (Account (sym, "long")) (Account (sym, "short"))

-- | The escrow contract that initialises the future. Both parties have to pay
--   their initial margin to this contract in order to unlock their tokens.
escrowParams
    :: SM.StateMachineClient FutureState FutureAction
    -> Future
    -> FutureAccounts
    -> FutureSetup
    -> EscrowParams DataValue
escrowParams client future ftos FutureSetup{longPK, shortPK, contractStart} =
    let
        address = Ledger.validatorHash $ Scripts.validatorScript $ SM.validatorInstance $ SM.scInstance client
        dataScript  = Ledger.DataValue $ PlutusTx.toData $ initialState future
        targets =
            [ Escrow.payToScriptTarget address
                dataScript
                (scale 2 (initialMargin future))
            , Escrow.payToPubKeyTarget (pubKeyHash longPK) (tokenFor Long ftos)
            , Escrow.payToPubKeyTarget (pubKeyHash shortPK) (tokenFor Short ftos)
            ]
    in EscrowParams
        { escrowDeadline = contractStart
        , escrowTargets = targets
        }

PlutusTx.makeLift ''Future
PlutusTx.makeLift ''FutureAccounts
PlutusTx.makeLift ''Margins
PlutusTx.makeIsData ''Margins
PlutusTx.makeLift ''Role
PlutusTx.makeIsData ''Role
PlutusTx.makeLift ''FutureState
PlutusTx.makeIsData ''FutureState
PlutusTx.makeLift ''FutureAction
PlutusTx.makeIsData ''FutureAction
