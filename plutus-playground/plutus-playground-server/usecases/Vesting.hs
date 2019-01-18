-- | Vesting scheme as a PLC contract
module Vesting where

import           Control.Monad                (void)

import qualified Language.PlutusTx            as PlutusTx
import qualified Ledger.Interval              as Interval
import qualified Language.PlutusTx.Prelude    as P
import           Ledger
import           Ledger.Validation
import           Wallet
import           Playground.Contract

-- | Tranche of a vesting scheme.
data VestingTranche = VestingTranche {
    vestingTrancheDate   :: Slot,
    vestingTrancheAmount :: Value
    } deriving (Generic, ToJSON, FromJSON, ToSchema)

PlutusTx.makeLift ''VestingTranche

-- | A vesting scheme consisting of two tranches. Each tranche defines a date
--   (slot) after which an additional amount of money can be spent.
data Vesting = Vesting {
    vestingTranche1 :: VestingTranche,
    vestingTranche2 :: VestingTranche,
    vestingOwner    :: PubKey
    } deriving (Generic, ToJSON, FromJSON, ToSchema)

PlutusTx.makeLift ''Vesting

-- | The total amount of money vested
totalAmount :: Vesting -> Value
totalAmount Vesting{..} =
    vestingTrancheAmount vestingTranche1 + vestingTrancheAmount vestingTranche2

-- | Data script for vesting utxo
data VestingData = VestingData {
    vestingDataHash    :: ValidatorHash, -- ^ Hash of the validator script
    vestingDataPaidOut :: Value -- ^ How much of the vested value has already been retrieved
    } deriving (Eq, Generic, ToJSON, FromJSON, ToSchema)

PlutusTx.makeLift ''VestingData

-- | Lock some funds with the vesting validator script and return a
--   [[VestingData]] representing the current state of the process
vestFunds :: Vesting -> Value -> MockWallet ()
vestFunds vst value = do
    _ <- if value < totalAmount vst then throwOtherError "Value must not be smaller than vested amount" else pure ()
    (payment, change) <- createPaymentWithChange value
    let contractAddress = Ledger.scriptAddress (validatorScript vst)
        dataScript      = DataScript (Ledger.lifted vd)
        vd =  VestingData (validatorScriptHash vst) 0
    payToScript_ defaultSlotRange contractAddress value dataScript

-- | Register this wallet as the owner of the vesting scheme. At each of the
--   two dates (tranche 1, tranche 2) we take out the funds that have been
--   released so far.
--   This function has to be called before the funds are vested, so that the
--   wallet can start watching the contract address for changes.
registerVestingOwner :: Vesting -> MockWallet ()
registerVestingOwner v = do
    ourPubKey <- ownPubKey
    let
        o = vestingOwner v
        addr = Ledger.scriptAddress (validatorScript v)
    _ <- if o /= ourPubKey
         then throwOtherError "Vesting scheme is not owned by this wallet"
         else startWatching addr

    register (tranche2Trigger v) (tranche2Handler v)
    -- ^ This runs `tranche2Handler` as soon as the final funds are released.
    --   It is possible to take out funds from tranche 1 earlier than that
    --   (as explained in the script code, below) but doing so requires some
    --   low-level code dealing with the transaction outputs, because we don't
    --   have a nice interface for this in 'Wallet.API' yet.


validatorScriptHash :: Vesting -> ValidatorHash
validatorScriptHash =
    plcValidatorDigest
    . Ledger.getAddress
    . Ledger.scriptAddress
    . validatorScript

validatorScript :: Vesting -> ValidatorScript
validatorScript v = ValidatorScript val where
    val = Ledger.applyScript inner (Ledger.lifted v)
    inner = Ledger.fromCompiledCode $$(PlutusTx.compile [|| \Vesting{..} () VestingData{..} (p :: PendingTx) ->
        let

            eqPk :: PubKey -> PubKey -> Bool
            eqPk = $$(eqPubKey)

            infixr 3 &&
            (&&) :: Bool -> Bool -> Bool
            (&&) = $$(P.and)

            PendingTx _ os _ _ _ range = p
            VestingTranche d1 (Value a1) = vestingTranche1
            VestingTranche d2 (Value a2) = vestingTranche2

            -- We assume here that the txn outputs are always given in the same
            -- order (1 PubKey output, followed by 0 or 1 script outputs)
            amountSpent :: Int
            amountSpent = case os of
                PendingTxOut (Value v') _ (PubKeyTxOut pk):_
                    | pk `eqPk` vestingOwner -> v'
                _ -> $$(P.error) ()

            -- Value that has been released so far under the scheme
            currentThreshold =
                if $$(Interval.contains) ($$(Interval.from) d1) range
                then if $$(Interval.contains) ($$(Interval.from) d2) range
                    -- everything can be spent
                        then a1 + a2
                        -- only the first tranche can be spent (we are between d1 and d2)
                        else a1
                -- Nothing has been released yet
                else 0


            paidOut = let Value v' = vestingDataPaidOut in v'
            newAmount = paidOut + amountSpent

            -- Verify that the amount taken out, plus the amount already taken
            -- out before, does not exceed the threshold that is currently
            -- allowed
            amountsValid = newAmount <= currentThreshold

            -- Check that the remaining output is locked by the same validation
            -- script
            txnOutputsValid = case os of
                _:PendingTxOut _ (Just (vl', _)) DataTxOut:_ -> $$(eqValidator) vl' vestingDataHash
                -- If there is no data script in the output list,
                -- we only accept the transaction if we are past the
                -- date of the final tranche.
                _ -> $$(Interval.before) d2 range

            isValid = amountsValid && txnOutputsValid
        in
        if isValid then () else $$(P.error) () ||])

tranche1Trigger :: Vesting -> EventTrigger
tranche1Trigger v =
    let VestingTranche dt1 _ = vestingTranche1 v in
    (slotRangeT (singleton dt1))

-- | Collect the remaining funds at the end of tranche 2
tranche2Handler :: Vesting -> EventHandler MockWallet
tranche2Handler vesting = EventHandler (\_ -> do
    logMsg "Collecting tranche 2"
    let vlscript = validatorScript vesting
        redeemerScript  = Ledger.unitRedeemer
        VestingTranche dt2 _ = vestingTranche2 vesting
        range = intervalFrom dt2
    collectFromScript range vlscript redeemerScript)

tranche2Trigger :: Vesting -> EventTrigger
tranche2Trigger v =
    let VestingTranche dt2 _ = vestingTranche2 v in
    (slotRangeT (singleton dt2))

$(mkFunctions ['vestFunds, 'registerVestingOwner])
