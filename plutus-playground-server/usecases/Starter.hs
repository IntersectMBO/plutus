{-# LANGUAGE TypeOperators       #-}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE DeriveAnyClass      #-}
{-# LANGUAGE DeriveGeneric       #-}
{-# LANGUAGE DerivingStrategies  #-}
{-# LANGUAGE NoImplicitPrelude   #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell     #-}
{-# LANGUAGE TypeApplications    #-}
{-# OPTIONS_GHC -fno-ignore-interface-pragmas #-}
module Starter where
-- TRIM TO HERE
-- This is a starter contract, based on the Game contract,
-- containing the bare minimum required scaffolding.
--
-- What you should change to something more suitable for
-- your use case:
--   * The DataScript type
--   * The Redeemer type
--
-- And add function implementations (and rename them to
-- something suitable) for the endpoints:
--   * publish
--   * redeem

import           Control.Monad              (void)
import qualified Language.PlutusTx          as PlutusTx
import           Language.PlutusTx.Prelude  hiding (Applicative (..))
import           Ledger                     (Address, DataScript (DataScript), PendingTx,
                                             RedeemerScript (RedeemerScript), ValidatorScript, mkValidatorScript,
                                             scriptAddress)
import           Ledger.Typed.Scripts       (wrapValidator)
import           Ledger.Value               (Value)
import           Playground.Contract
import           Language.Plutus.Contract
import           Language.Plutus.Contract.Tx (payToScript, collectFromScript)

-- | These are the data script and redeemer types. We are using an integer
--   value for both, but you should define your own types.
newtype DataValue = DataValue Integer deriving newtype PlutusTx.IsData
PlutusTx.makeLift ''DataValue

newtype RedeemerValue = RedeemerValue Integer deriving newtype PlutusTx.IsData
PlutusTx.makeLift ''RedeemerValue

-- | This method is the spending validator (which gets lifted to
--   its on-chain representation).
validateSpend :: DataValue -> RedeemerValue -> PendingTx -> Bool
validateSpend _dataValue _redeemerValue _ = error () -- Please provide an implementation.

-- | This function lifts the validator previously defined to
--   the on-chain representation.
contractValidator :: ValidatorScript
contractValidator =
    mkValidatorScript $$(PlutusTx.compile [|| wrap validateSpend ||])
    where wrap = wrapValidator @DataValue @RedeemerValue

-- | Helper function used to build the DataScript.
mkDataScript :: Integer -> DataScript
mkDataScript =
    DataScript . PlutusTx.toData . DataValue

-- | Helper function used to build the RedeemerScript.
mkRedeemerScript :: Integer -> RedeemerScript
mkRedeemerScript =
    RedeemerScript . PlutusTx.toData . RedeemerValue

-- | The address of the contract (the hash of its validator script).
contractAddress :: Address
contractAddress = Ledger.scriptAddress contractValidator

-- | The schema of the contract, with two endpoints.
type Schema =
    BlockchainActions
        .\/ Endpoint "publish" (Integer, Value)
        .\/ Endpoint "redeem" Integer

contract :: Contract Schema e ()
contract = publish <|> redeem

-- | The "publish" contract endpoint.
publish :: Contract Schema e ()
publish = do
    (dataValue, lockedFunds) <- endpoint @"publish"
    let tx = payToScript lockedFunds contractAddress (mkDataScript dataValue)
    void $ writeTx tx

-- | The "redeem" contract endpoint.
redeem :: Contract Schema e ()
redeem = do
    redeemerValue <- endpoint @"redeem"
    unspentOutputs <- utxoAt contractAddress
    let redeemer = mkRedeemerScript redeemerValue
        tx = collectFromScript unspentOutputs contractValidator redeemer
    void $ writeTx tx

endpoints :: Contract Schema e ()
endpoints = contract

mkSchemaDefinitions ''Schema
    