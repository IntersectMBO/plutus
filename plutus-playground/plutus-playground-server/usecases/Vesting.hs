-- | Vesting scheme as a PLC contract
module Language.PlutusTx.Coordination.Contracts.Vesting  where

import           Control.Monad.Error.Class    (MonadError (..))
import           Control.Monad                (void)
import           Data.Aeson                   (FromJSON, ToJSON)
import qualified Data.Set                     as Set
import           GHC.Generics                 (Generic)
import           Ledger.Validation            (Height (..), PendingTx (..), PendingTxOut (..), PendingTxOutType (..),
                                              ValidatorHash)
import qualified Language.PlutusTx            as PlutusTx
import           Ledger                       (DataScript (..), PubKey (..), TxOutRef', ValidatorScript(..), Value (..), scriptTxIn, scriptTxOut)
import qualified Ledger                       as Ledger
import qualified Ledger.Validation            as Validation
import           Prelude                      hiding ((&&))
import           Playground.Contract
import           Wallet                       (WalletAPI (..), WalletAPIError, otherError, ownPubKeyTxOut, signAndSubmit)

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
vestFunds :: (
    MonadError WalletAPIError m,
    WalletAPI m)
    => Vesting
    -> Value
    -> m ()
vestFunds vst value = do
    _ <- if value < totalAmount vst then otherError "Value must not be smaller than vested amount" else pure ()
    (payment, change) <- createPaymentWithChange value
    let vs = validatorScript vst
        o = scriptTxOut value vs (DataScript $ Ledger.lifted vd)
        vd =  VestingData (validatorScriptHash vst) 0
    void $ signAndSubmit payment [o, change]

-- | Retrieve some of the vested funds.
retrieveFunds :: (
    Monad m,
    WalletAPI m)
    => Vesting
    -> VestingData -- ^ Value that has already been taken out
    -> TxOutRef'  -- ^ Transaction output locked by the vesting validator script
    -> Ledger.Value -- ^ Value we want to take out now
    -> m ()
retrieveFunds vs vd r vnow = do
    oo <- ownPubKeyTxOut vnow
    let val = validatorScript vs
        o   = scriptTxOut remaining val (DataScript $ Ledger.lifted vd')
        remaining = totalAmount vs - vnow
        vd' = vd {vestingDataPaidOut = vnow + vestingDataPaidOut vd }
        inp = scriptTxIn r val Ledger.unitRedeemer
    void $ signAndSubmit (Set.singleton inp) [oo, o]

validatorScriptHash :: Vesting -> ValidatorHash
validatorScriptHash =
    Validation.plcValidatorDigest
    . Ledger.getAddress
    . Ledger.scriptAddress
    . validatorScript

validatorScript :: Vesting -> ValidatorScript
validatorScript v = ValidatorScript val where
    val = Ledger.applyScript inner (Ledger.lifted v)
    inner = Ledger.fromPlcCode $$(PlutusTx.plutus [|| \Vesting{..} () VestingData{..} (p :: PendingTx ValidatorHash) ->
        let

            eqBs :: ValidatorHash -> ValidatorHash -> Bool
            eqBs = $$(Validation.eqValidator)

            eqPk :: PubKey -> PubKey -> Bool
            eqPk = $$(Validation.eqPubKey)

            infixr 3 &&
            (&&) :: Bool -> Bool -> Bool
            (&&) = $$(PlutusTx.and)

            PendingTx _ os _ _ (Height h) _ _ = p
            VestingTranche (Height d1) (Value a1) = vestingTranche1
            VestingTranche (Height d2) (Value a2) = vestingTranche2

            -- We assume here that the txn outputs are always given in the same
            -- order (1 PubKey output, followed by 0 or 1 script outputs)
            amountSpent :: Int
            amountSpent = case os of
                PendingTxOut (Value v') _ (PubKeyTxOut pk):_
                    | pk `eqPk` vestingOwner -> v'
                _ -> $$(PlutusTx.error) ()

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
                _ -> $$(PlutusTx.error) ()

            isValid = amountsValid && txnOutputsValid
        in
        if isValid then () else $$(PlutusTx.error) () ||])

$(mkFunction 'vestFunds)
$(mkFunction 'retrieveFunds)
