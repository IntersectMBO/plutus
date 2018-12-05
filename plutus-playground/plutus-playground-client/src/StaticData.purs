module StaticData
  ( editorContents
  ) where

import Data.Map (Map)
import Data.Map as Map
import Data.Tuple.Nested ((/\))

editorContents :: Map String String
editorContents =
  Map.fromFoldable
    [ "Vesting" /\ vesting
    , "Game" /\ game
    , "Crowdfunding" /\ crowdfunding
    , "Messages" /\ messages
    ]

vesting :: String
vesting = """-- | Vesting scheme as a PLC contract
{-# LANGUAGE DataKinds         #-}
{-# LANGUAGE DeriveGeneric     #-}
{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards   #-}
{-# LANGUAGE TemplateHaskell   #-}
{-# OPTIONS -fplugin=Language.PlutusTx.Plugin -fplugin-opt Language.PlutusTx.Plugin:dont-typecheck #-}
module Language.PlutusTx.Coordination.Contracts.Vesting  where

import           Control.Monad.Error.Class    (MonadError (..))
import           Control.Monad                (void)
import           Data.Aeson                   (FromJSON, ToJSON)
import qualified Data.Set                     as Set
import           GHC.Generics                 (Generic)
import           Ledger.Validation            (Height (..), PendingTx (..), PendingTxOut (..), PendingTxOutType (..),
                                              ValidatorHash)
import qualified Language.PlutusTx            as PlutusTx
import qualified Language.PlutusTx.Validation as PlutusTx
import           Ledger                       (DataScript (..), PubKey (..), TxOutRef', Validator (..), Value (..), scriptTxIn, scriptTxOut)
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

validatorScript :: Vesting -> Validator
validatorScript v = Validator val where
    val = Ledger.applyScript inner (Ledger.lifted v)
    inner = Ledger.fromPlcCode $$(PlutusTx.plutus [|| \Vesting{..} () VestingData{..} (p :: PendingTx ValidatorHash) ->
        let

            eqBs :: ValidatorHash -> ValidatorHash -> Bool
            eqBs = $$(PlutusTx.eqValidator)

            eqPk :: PubKey -> PubKey -> Bool
            eqPk = $$(PlutusTx.eqPubKey)

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
                _ -> PlutusTx.error ()

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
                _ -> PlutusTx.error ()

            isValid = amountsValid && txnOutputsValid
        in
        if isValid then () else PlutusTx.error () ||])

$(mkFunction 'vestFunds)
"""

game :: String
game = """{-# OPTIONS -fplugin=Language.PlutusTx.Plugin -fplugin-opt Language.PlutusTx.Plugin:dont-typecheck #-}
module Language.PlutusTx.Coordination.Contracts.Game where


import           Control.Applicative          (Applicative (..))
import           Control.Lens
import           Control.Monad                (void)
import           Data.Foldable                (foldMap)
import qualified Data.Map                     as Map
import           Data.Maybe                   (fromMaybe)
import           Data.Monoid                  (Sum (..))
import qualified Data.Set                     as Set
import           GHC.Generics                 (Generic)
import           Playground.Contract
import           Data.Text
import           Control.Monad.Error (MonadError(..))

import qualified Language.PlutusTx            as PlutusTx
import qualified Language.PlutusTx.Validation as PlutusTx
import           Ledger as Ledger
import           Ledger.Validation
import Wallet hiding (payToPubKey)

logAMessage :: (WalletAPI m, WalletDiagnostics m) => m ()
logAMessage = logMsg "wallet log"

data ANumber = ANumber Int
    deriving (Generic, ToJSON, FromJSON, ToSchema)

PlutusTx.makeLift ''ANumber

data AGuess = AGuess Int
    deriving (Generic, ToJSON, FromJSON, ToSchema)

PlutusTx.makeLift ''AGuess

gameValidator :: ValidatorScript
gameValidator = ValidatorScript (Ledger.fromPlcCode $$(PlutusTx.plutus [||
    \(AGuess guess) (ANumber number) (p :: PendingTx ValidatorHash) ->

    if guess == number
    then ()
    else $$(PlutusTx.traceH) "WRONG!" (PlutusTx.error ())

    ||]))

gameAddress :: Address'
gameAddress = Ledger.scriptAddress gameValidator

contribute :: (WalletAPI m, WalletDiagnostics m)
    => Int
    -> Value
    -> m ()
contribute n value = do
    let ds = DataScript (Ledger.lifted (ANumber n))
    _ <- payToScript gameAddress value ds
    pure ()

guess :: (WalletAPI m, WalletDiagnostics m)
    => Int
    -> m ()
guess n = do
    let redeemer = RedeemerScript (Ledger.lifted (AGuess n))
    collectFromScript gameValidator redeemer
    -- won't worK! We need to start watching the address first!

$(mkFunction 'logAMessage)
$(mkFunction 'contribute)
$(mkFunction 'guess)
"""

crowdfunding :: String
crowdfunding = """-- | Crowdfunding contract implemented using the [[Plutus]] interface.
-- This is the fully parallel version that collects all contributions
-- in a single transaction. This is, of course, limited by the maximum
-- number of inputs a transaction can have.
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE DeriveGeneric       #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE RecordWildCards     #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell     #-}
{-# LANGUAGE TypeApplications    #-}
{-# OPTIONS -fplugin=Language.PlutusTx.Plugin -fplugin-opt Language.PlutusTx.Plugin:dont-typecheck #-}
module Language.PlutusTx.Coordination.Contracts.CrowdFunding where

import           Control.Applicative          (Applicative (..))
import           Control.Lens
import           Control.Monad                (void)
import           Data.Foldable                (foldMap)
import qualified Data.Map                     as Map
import           Data.Maybe                   (fromMaybe)
import           Data.Monoid                  (Sum (..))
import qualified Data.Set                     as Set
import           GHC.Generics                 (Generic)
import           Playground.Contract

import qualified Language.PlutusTx            as PlutusTx
import qualified Language.PlutusTx.Validation as PlutusTx
import           Ledger                       (DataScript (..), PubKey (..), TxId', Validator (..), Value (..), scriptTxIn, Tx)
import qualified Ledger                       as Ledger
import           Ledger.Validation            (Height (..), PendingTx (..), PendingTxIn (..), PendingTxOut, ValidatorHash)
import           Wallet                       (EventHandler (..), EventTrigger, Range (..), WalletAPI (..),
                                               WalletDiagnostics (..), andT, blockHeightT, fundsAtAddressT, otherError,
                                               ownPubKeyTxOut, payToScript, pubKey, signAndSubmit)

-- | A crowdfunding campaign.
data Campaign = Campaign
    { campaignDeadline           :: Height
    , campaignTarget             :: Value
    , campaignCollectionDeadline :: Height
    , campaignOwner              :: CampaignActor
    } deriving (Generic, ToJSON, FromJSON, ToSchema)

type CampaignActor = PubKey

PlutusTx.makeLift ''Campaign

data CampaignAction = Collect | Refund
    deriving (Generic, ToJSON, FromJSON, ToSchema)

PlutusTx.makeLift ''CampaignAction

-- | Contribute funds to the campaign (contributor)
--
contribute :: (WalletAPI m, WalletDiagnostics m)
    => Campaign
    -> Value
    -> m ()
contribute cmp value = do
    _ <- if value <= 0 then otherError "Must contribute a positive value" else pure ()
    ds <- DataScript . Ledger.lifted . pubKey <$> myKeyPair

    tx <- payToScript (campaignAddress cmp) value ds
    logMsg "Submitted contribution"

    register (refundTrigger cmp) (refund (Ledger.hashTx tx) cmp)
    logMsg "Registered refund trigger"

-- | Register a [[EventHandler]] to collect all the funds of a campaign
--
collect :: (WalletAPI m, WalletDiagnostics m) => Campaign -> m ()
collect cmp = register (collectFundsTrigger cmp) $ EventHandler $ \_ -> do
        logMsg "Collecting funds"
        am <- watchedAddresses
        let scr        = contributionScript cmp
            contributions = am ^. at (campaignAddress cmp) . to (Map.toList . fromMaybe Map.empty)
            red        = Ledger.Redeemer $ Ledger.lifted Collect
            con (r, _) = scriptTxIn r scr red
            ins        = con <$> contributions
            value = getSum $ foldMap (Sum . snd) contributions

        oo <- ownPubKeyTxOut value
        void $ signAndSubmit (Set.fromList ins) [oo]


-- | The address of a [[Campaign]]
campaignAddress :: Campaign -> Ledger.Address'
campaignAddress = Ledger.scriptAddress . contributionScript

-- | The validator script that determines whether the campaign owner can
--   retrieve the funds or the contributors can claim a refund.
--
--   Assume there is a campaign `c :: Campaign` with two contributors
--   (identified by public key pc_1 and pc_2) and one campaign owner (pco).
--   Each contributor creates a transaction, t_1 and t_2, whose outputs are
--   locked by the scripts `contributionScript c pc_1` and `contributionScript
--   c pc_1` respectively.
--   There are two outcomes for the campaign.
--   1. Campaign owner collects the funds from both contributors. In this case
--      the owner creates a single transaction with two inputs, referring to
--      t_1 and t_2. Each input contains the script `contributionScript c`
--      specialised to a contributor. This case is covered by the
--      definition for `payToOwner` below.
--   2. Refund. In this case each contributor creates a transaction with a
--      single input claiming back their part of the funds. This case is
--      covered by the `refundable` branch.
contributionScript :: Campaign -> Validator
contributionScript cmp  = Validator val where
    val = Ledger.applyScript inner (Ledger.lifted cmp)

    --   See note [Contracts and Validator Scripts] in
    --       Language.Plutus.Coordination.Contracts
    inner = Ledger.fromPlcCode $$(PlutusTx.plutus [|| (\Campaign{..} (act :: CampaignAction) (a :: CampaignActor) (p :: PendingTx ValidatorHash) ->
        let

            infixr 3 &&
            (&&) :: Bool -> Bool -> Bool
            (&&) = $$(PlutusTx.and)

            -- | Check that a pending transaction is signed by the private key
            --   of the given public key.
            signedByT :: PendingTx ValidatorHash -> CampaignActor -> Bool
            signedByT = $$(PlutusTx.txSignedBy)

            PendingTx ps outs _ _ (Height h) _ _ = p

            deadline :: Int
            deadline = let Height h' = campaignDeadline in h'

            collectionDeadline :: Int
            collectionDeadline = let Height h' = campaignCollectionDeadline in h'

            target :: Int
            target = let Value v = campaignTarget in v

            -- | The total value of all contributions
            totalInputs :: Int
            totalInputs =
                let v (PendingTxIn _ _ (Value vl)) = vl in
                $$(PlutusTx.foldr) (\i total -> total + v i) 0 ps

            isValid = case act of
                Refund -> -- the "refund" branch
                    let
                        -- Check that all outputs are paid to the public key
                        -- of the contributor (that is, to the `a` argument of the data script)

                        contributorTxOut :: PendingTxOut -> Bool
                        contributorTxOut o = $$(PlutusTx.maybe) False (\pk -> $$(PlutusTx.eqPubKey) pk a) ($$(PlutusTx.pubKeyOutput) o)

                        contributorOnly = $$(PlutusTx.all) contributorTxOut outs

                        refundable   = h > collectionDeadline &&
                                                    contributorOnly &&
                                                    signedByT p a

                    in refundable
                Collect -> -- the "successful campaign" branch
                    let
                        payToOwner = h > deadline &&
                                    h <= collectionDeadline &&
                                    totalInputs >= target &&
                                    signedByT p campaignOwner
                    in payToOwner
        in
        if isValid then () else PlutusTx.error ()) ||])

-- | An event trigger that fires when a refund of campaign contributions can be claimed
refundTrigger :: Campaign -> EventTrigger
refundTrigger c = andT
    (fundsAtAddressT (campaignAddress c) $ GEQ 1)
    (blockHeightT (GEQ $ fromIntegral $ succ $ getHeight $ campaignCollectionDeadline c))

-- | An event trigger that fires when the funds for a campaign can be collected
collectFundsTrigger :: Campaign -> EventTrigger
collectFundsTrigger c = andT
    (fundsAtAddressT (campaignAddress c) $ GEQ $ campaignTarget c)
    (blockHeightT $ fromIntegral . getHeight <$> Interval (campaignDeadline c) (campaignCollectionDeadline c))

-- | Claim a refund of our campaign contribution
refund :: (WalletAPI m, WalletDiagnostics m) => TxId' -> Campaign -> EventHandler m
refund txid cmp = EventHandler $ \_ -> do
    logMsg "Claiming refund"
    am <- watchedAddresses
    let adr     = campaignAddress cmp
        utxo    = fromMaybe Map.empty $ am ^. at adr
        ourUtxo = Map.toList $ Map.filterWithKey (\k _ -> txid == Ledger.txOutRefId k) utxo
        scr   = contributionScript cmp
        red   = Ledger.Redeemer $ Ledger.lifted Refund
        i ref = scriptTxIn ref scr red
        inputs = Set.fromList $ i . fst <$> ourUtxo
        value  = getSum $ foldMap (Sum . snd) ourUtxo

    out <- ownPubKeyTxOut value
    void $ signAndSubmit inputs [out]

$(mkFunction 'collect)
$(mkFunction 'contribute)
"""

messages :: String
messages = """-- Contract endpoints that generate different kinds of errors for the log:
-- logAMessage produces a log message from a wallet
-- submitInvalidTxn submits an invalid txn which should result in a "Validation failed" message
-- throwWalletAPIError throws an error from a wallet (client)
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE DeriveGeneric       #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE RecordWildCards     #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell     #-}
{-# LANGUAGE TypeApplications    #-}
{-# OPTIONS -fplugin=Language.PlutusTx.Plugin -fplugin-opt Language.PlutusTx.Plugin:dont-typecheck #-}
module Language.PlutusTx.Coordination.Contracts.Messages where

import           Control.Applicative          (Applicative (..))
import           Control.Lens
import           Control.Monad                (void)
import           Data.Foldable                (foldMap)
import qualified Data.Map                     as Map
import           Data.Maybe                   (fromMaybe)
import           Data.Monoid                  (Sum (..))
import qualified Data.Set                     as Set
import           GHC.Generics                 (Generic)
import           Playground.Contract
import           Data.Text
import           Control.Monad.Error (MonadError(..))

import qualified Language.PlutusTx            as PlutusTx
import qualified Language.PlutusTx.Validation as PlutusTx
import           Ledger as Ledger
import           Ledger.Validation
import           Wallet

logAMessage :: (WalletAPI m, WalletDiagnostics m) => m ()
logAMessage = logMsg "wallet log"

submitInvalidTxn :: (WalletAPI m, WalletDiagnostics m) => m ()
submitInvalidTxn = do
    logMsg "Preparing to submit an invalid transaction"
    let tx = Tx
            { txInputs = Set.empty
            , txOutputs = []
            , txForge = 2
            , txFee = 0
            , txSignatures = []
            }
    submitTxn tx

throwWalletAPIError :: (WalletAPI m, WalletDiagnostics m) => Text -> m ()
throwWalletAPIError = throwError . OtherError

$(mkFunction 'logAMessage)
$(mkFunction 'submitInvalidTxn)
$(mkFunction 'throwWalletAPIError)
"""
