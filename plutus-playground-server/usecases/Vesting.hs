{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE DeriveGeneric       #-}
{-# LANGUAGE DeriveAnyClass      #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE RecordWildCards     #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell     #-}
{-# LANGUAGE TypeApplications    #-}
module Vesting where
-- TRIM TO HERE
-- Vesting scheme as a PLC contract
import           Control.Monad                (void)
import qualified Data.Map                  as Map
import qualified Data.Set                  as Set

import qualified Language.PlutusTx         as P
import           Ledger                    (Address, DataScript(..), RedeemerScript(..), Signature, Slot, TxOutRef, TxIn, ValidatorScript(..))
import qualified Ledger                    as Ledger
import           Ledger.Value              (Value)
import qualified Ledger.Value              as Value
import qualified Ledger.Value              as Value.TH
import qualified Ledger.Interval           as Interval
import qualified Ledger.Slot               as Slot
import qualified Ledger.Validation         as V
import           Ledger.Validation         (PendingTx(..))
import qualified Ledger.Value              as Value
import           Wallet                    (WalletAPI(..), WalletDiagnostics, PubKey)
import qualified Wallet                    as W
import qualified Wallet.API                as WAPI
import qualified Wallet.Emulator.Types     as EM
import           Playground.Contract

{- |
    A simple vesting scheme. Money is locked by a contract and may only be
    retrieved after some time has passed.

    This is our first example of a contract that covers multiple transactions,
    with a contract state that changes over time.

    In our vesting scheme the money will be released in two _tranches_ (parts):
    A smaller part will be available after an initial number of slots have
    passed, and the entire amount will be released at the end. The owner of the
    vesting scheme does not have to take out all the money at once: They can take out any amount up to the total that has been released so far. The remaining funds stay locked and can be retrieved later.

    Let's start with the data types.

-}

-- | Tranche of a vesting scheme.
data VestingTranche = VestingTranche {
    vestingTrancheDate   :: Slot,
    -- ^ When this tranche is released
    vestingTrancheAmount :: Value
    -- ^ How much money is locked in this tranche
    } deriving (Generic, ToJSON, FromJSON, ToSchema)

P.makeLift ''VestingTranche

-- | A vesting scheme consisting of two tranches. Each tranche defines a date
--   (slot) after which an additional amount of money can be spent.
data Vesting = Vesting {
    vestingTranche1 :: VestingTranche,
    -- ^ First tranche

    vestingTranche2 :: VestingTranche,
    -- ^ Second tranche

    vestingOwner    :: PubKey
    -- ^ The recipient of the scheme (who is authorised to take out money once
    --   it has been released)
    } deriving (Generic, ToJSON, FromJSON, ToSchema)

P.makeLift ''Vesting

-- | The total value locked by a vesting scheme
totalAmount :: Vesting -> Value
totalAmount (Vesting l r _) = (vestingTrancheAmount l) `Value.plus` (vestingTrancheAmount r)

-- | The amount guaranteed to be available from a given tranche in a given slot range.
{-# INLINABLE availableFrom #-}
availableFrom :: VestingTranche -> Slot.SlotRange -> Value
availableFrom (VestingTranche d v) range =
    -- The valid range is an open-ended range starting from the tranche vesting date
    let validRange = Interval.from d
    -- If the valid range completely contains the argument range (meaning in particular
    -- that the start slot of the argument range is after the tranche vesting date), then
    -- the money in the tranche is available, otherwise nothing is available.
    in if validRange `Slot.contains` range then v else Value.zero

{- |

    What should our data and redeemer scripts be? The vesting scheme only has a
    single piece of information that we need to keep track of, namely how much
    money is still locked in the contract. We can get this information from the
    contract's transaction output, so we don't need to store it in the data
    script. The type of our data script is therefore `()`.

    The redeemer script should carry some proof that the retriever of the funds
    is indeed the `vestingOwner` that was specified in the contract. This proof
    takes the form of a transaction hash signed by the `vestingOwner`'s private
    key. For this we use the type 'Ledger.Crypto.Signature'

    That gives our validator script the signature

    `Vesting -> Signature -> () -> PendingTx -> ()`

-}

-- | The validator script
mkValidator :: Vesting -> () -> () -> PendingTx -> ()
mkValidator d@Vesting{..} () () p@PendingTx{pendingTxValidRange = range} =
    let
        -- We need the hash of this validator script in order to ensure
        -- that the pending transaction locks the remaining amount of funds
        -- at the contract address.
        ownHash = V.ownHash p

        -- Value that has been released so far under the scheme
        released = availableFrom vestingTranche1 range
            `Value.plus` availableFrom vestingTranche2 range

        -- And the following amount has not been released yet:
        unreleased :: Value
        unreleased = (totalAmount d) `Value.minus` released

        -- To check whether the withdrawal is legitimate we need to
        -- 1. Ensure that the amount taken out does not exceed the current
        --    limit
        -- 2. Compare the provded signature with the public key of the
        --    vesting owner
        -- We will call these conditions con1 and con2.

        -- con1 is true if the amount that remains locked in the contract
        -- is greater than or equal to 'unreleased'. We use the
        -- `valueLockedBy` function to get the value paid by pending
        -- transaction 'p' to the script address 'ownHash'.
        con1 :: Bool
        con1 =
            let remaining = V.valueLockedBy p ownHash
            in remaining `Value.geq` unreleased

        -- con2 is true if the scheme owner has signed the pending
        -- transaction 'p'.
        con2 :: Bool
        con2 = p `V.txSignedBy` vestingOwner
    in
        if con1 `P.and` con2
        then ()
        else P.traceErrorH "Cannot withdraw"

validatorScript :: Vesting -> ValidatorScript
validatorScript v = ValidatorScript $
    $$(Ledger.compileScript [|| mkValidator ||])
        `Ledger.applyScript`
            Ledger.lifted v

contractAddress :: Vesting -> Address
contractAddress vst = Ledger.scriptAddress (validatorScript vst)

{- |

    We need three endpoints:

    * 'vestFunds' to lock the funds in a vesting scheme
    * 'registerVestingScheme', used by the owner to start watching the scheme's address
    * 'withdraw', used by the owner to take out some funds.

    The first two are very similar to endpoints we defined for earlier
    contracts.

-}

vestFunds :: (Monad m, WalletAPI m) => Vesting -> m ()
vestFunds vst = do
    let amt = totalAmount vst
        adr = contractAddress vst
        dataScript = DataScript (Ledger.lifted ())
    W.payToScript_ W.defaultSlotRange adr amt dataScript

registerVestingScheme :: (WalletAPI m) =>  Vesting -> m ()
registerVestingScheme vst = startWatching (contractAddress vst)

{- |

    The last endpoint, `withdraw`, is different. We need to create a
    transaction that spends the contract's current unspent transaction output
    *and* puts the value that remains back at the script address.

-}
withdraw :: (Monad m, WalletAPI m) => Vesting -> Value -> m ()
withdraw vst vl = do

    let address = contractAddress vst
        validator = validatorScript vst

    -- We are going to use the wallet API to build the transaction "by hand",
    -- that is without using 'collectFromScript'.
    -- The signature of 'createTxAndSubmit' is
    -- 'SlotRange -> Set.Set TxIn -> [TxOut] -> m Tx'. So we need a slot range,
    -- a set of inputs and a list of outputs.

    -- The transaction's validity range should begin with the current slot and
    -- last indefinitely.
    range <- fmap WAPI.intervalFrom WAPI.slot

    -- The input should be the UTXO of the vesting scheme. We can get the
    -- outputs at an address (as far as they are known by the wallet) with
    -- `outputsAt`, which returns a map of 'TxOutRef' to 'TxOut'.
    utxos <- WAPI.outputsAt address

    let
        -- the redeemer script with the unit value ()
        redeemer  = RedeemerScript (Ledger.lifted ())

        -- Turn the 'utxos' map into a set of 'TxIn' values
        mkIn :: TxOutRef -> TxIn
        mkIn r = Ledger.scriptTxIn r validator redeemer

        ins = Set.map mkIn (Map.keysSet utxos)

    -- Our transaction has either one or two outputs.
    -- If the scheme is finished (no money is left in it) then
    -- there is only one output, a pay-to-pubkey output owned by
    -- us.
    -- If any money is left in the scheme then there will be an additional
    -- pay-to-script output locked by the vesting scheme's validator script
    -- that keeps the remaining value.

    -- We can create a public key output to our own key with 'ownPubKeyTxOut'.
    ownOutput <- W.ownPubKeyTxOut vl

    -- Now to compute the difference between 'vl' and what is currently in the
    -- scheme:
    let
        currentlyLocked = Map.foldr (\txo vl' -> vl' `Value.plus` Ledger.txOutValue txo) Value.zero utxos
        remaining = currentlyLocked `Value.minus` vl

        otherOutputs = if Value.eq Value.zero remaining
                       then []
                       else [Ledger.scriptTxOut remaining validator (DataScript (Ledger.lifted ()))]

    -- Finally we have everything we need for `createTxAndSubmit`
    _ <- WAPI.createTxAndSubmit range ins (ownOutput:otherOutputs)

    pure ()

$(mkFunctions ['vestFunds, 'registerVestingScheme, 'withdraw])
