-- | Vesting scheme as a PLC contract
module Language.PlutusTx.Coordination.Contracts.Vesting  where

import           Control.Monad                (void)
import qualified Data.Set                     as Set

import qualified Language.PlutusTx            as PlutusTx
import qualified Language.PlutusTx.Prelude    as P
import           Ledger
import           Ledger.Validation
import           Wallet
import           Playground.Contract

-- | Tranche of a vesting scheme.
data VestingTranche = VestingTranche {
    vestingTrancheDate   :: Height,
    vestingTrancheAmount :: Value
    } deriving (Generic, ToJSON, FromJSON, ToSchema)

PlutusTx.makeLift ''VestingTranche

-- | A vesting scheme consisting of two tranches. Each tranche defines a date
--   (block height) after which an additional amount of money can be spent.
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
    _ <- if value < totalAmount vst then otherError "Value must not be smaller than vested amount" else pure ()
    (payment, change) <- createPaymentWithChange value
    let contractAddress = Ledger.scriptAddress (validatorScript vst)
        dataScript      = DataScript (Ledger.lifted vd)
        vd =  VestingData (validatorScriptHash vst) 0
    void (payToScript contractAddress value dataScript)

-- | Retrieve some of the vested funds.
retrieveFunds :: 
    Vesting
    -> VestingData -- ^ Value that has already been taken out
    -> TxOutRef'  -- ^ Transaction output locked by the vesting validator script
    -> Ledger.Value -- ^ Value we want to take out now
    -> MockWallet ()
retrieveFunds vs vd r vnow = do
    oo <- ownPubKeyTxOut vnow
    let val = validatorScript vs
        o   = scriptTxOut remaining val (DataScript $ Ledger.lifted vd')
        remaining = totalAmount vs - vnow
        vd' = vd {vestingDataPaidOut = vnow + vestingDataPaidOut vd }
        inp = scriptTxIn r val Ledger.unitRedeemer
    void (signAndSubmit (Set.singleton inp) [oo, o])

validatorScriptHash :: Vesting -> ValidatorHash
validatorScriptHash =
    plcValidatorDigest
    . Ledger.getAddress
    . Ledger.scriptAddress
    . validatorScript

validatorScript :: Vesting -> ValidatorScript
validatorScript v = ValidatorScript val where
    val = Ledger.applyScript inner (Ledger.lifted v)
    inner = Ledger.fromPlcCode $$(PlutusTx.plutus [|| \Vesting{..} () VestingData{..} (p :: PendingTx ValidatorHash) ->
        let

            eqBs :: ValidatorHash -> ValidatorHash -> Bool
            eqBs = $$(eqValidator)

            eqPk :: PubKey -> PubKey -> Bool
            eqPk = $$(eqPubKey)

            infixr 3 &&
            (&&) :: Bool -> Bool -> Bool
            (&&) = $$(P.and)

            PendingTx _ os _ _ (Height h) _ _ = p
            VestingTranche (Height d1) (Value a1) = vestingTranche1
            VestingTranche (Height d2) (Value a2) = vestingTranche2

            -- We assume here that the txn outputs are always given in the same
            -- order (1 PubKey output, followed by 0 or 1 script outputs)
            amountSpent :: Int
            amountSpent = case os of
                PendingTxOut (Value v') _ (PubKeyTxOut pk):_
                    | pk `eqPk` vestingOwner -> v'
                _ -> $$(P.error) ()

            -- Value that has been released so far under the scheme
            currentThreshold =
                if h >= d1
                then if h >= d2
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
                _:PendingTxOut _ (Just (vl', _)) DataTxOut:_ ->
                    vl' `eqBs` vestingDataHash
                _ -> $$(P.error) ()

            isValid = amountsValid && txnOutputsValid
        in
        if isValid then () else $$(P.error) () ||])

$(mkFunction 'vestFunds)
$(mkFunction 'retrieveFunds)
