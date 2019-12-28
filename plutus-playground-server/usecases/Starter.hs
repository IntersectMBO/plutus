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
--   * The MyDataValue type
--   * The MyMyRedeemerValue type
--
-- And add function implementations (and rename them to
-- something suitable) for the endpoints:
--   * publish
--   * redeem

import           Control.Monad              (void)
import qualified Language.PlutusTx          as PlutusTx
import           Language.PlutusTx.Prelude  hiding (Applicative (..))
import           Ledger                     (Address, DataValue (DataValue), PendingTx,
                                             RedeemerValue (RedeemerValue), Validator, mkValidatorScript,
                                             scriptAddress)
import           Ledger.Typed.Scripts       (wrapValidator)
import           Ledger.Value               (Value)
import           Playground.Contract
import           Language.Plutus.Contract
import           Language.Plutus.Contract.Tx (payToScript, collectFromScript)

-- | These are the data script and redeemer types. We are using an integer
--   value for both, but you should define your own types.
newtype MyDataValue = MyDataValue Integer deriving newtype PlutusTx.IsData
PlutusTx.makeLift ''MyDataValue

newtype MyRedeemerValue = MyRedeemerValue Integer deriving newtype PlutusTx.IsData
PlutusTx.makeLift ''MyRedeemerValue

-- | This method is the spending validator (which gets lifted to
--   its on-chain representation).
validateSpend :: MyDataValue -> MyRedeemerValue -> PendingTx -> Bool
validateSpend _myDataValue _myRedeemerValue _ = error () -- Please provide an implementation.

-- | This function lifts the validator previously defined to
--   the on-chain representation.
contractValidator :: Validator
contractValidator =
    mkValidatorScript $$(PlutusTx.compile [|| wrap validateSpend ||])
    where wrap = wrapValidator @MyDataValue @MyRedeemerValue

-- | Helper function used to build the DataValue.
mkDataValue :: Integer -> DataValue
mkDataValue =
    DataValue . PlutusTx.toData . MyDataValue

-- | Helper function used to build the RedeemerValue.
mkRedeemerValue :: Integer -> RedeemerValue
mkRedeemerValue =
    RedeemerValue . PlutusTx.toData . MyRedeemerValue

-- | The address of the contract (the hash of its validator script).
contractAddress :: Address
contractAddress = Ledger.scriptAddress contractValidator

-- | The schema of the contract, with two endpoints.
type Schema =
    BlockchainActions
        .\/ Endpoint "publish" (Integer, Value)
        .\/ Endpoint "redeem" Integer

contract :: AsContractError e => Contract Schema e ()
contract = publish <|> redeem

-- | The "publish" contract endpoint.
publish :: AsContractError e => Contract Schema e ()
publish = do
    (myDataValue, lockedFunds) <- endpoint @"publish"
    let tx = payToScript lockedFunds contractAddress (mkDataValue myDataValue)
    void $ submitTx tx

-- | The "redeem" contract endpoint.
redeem :: AsContractError e => Contract Schema e ()
redeem = do
    myRedeemerValue <- endpoint @"redeem"
    unspentOutputs <- utxoAt contractAddress
    let redeemer = mkRedeemerValue myRedeemerValue
        tx = collectFromScript unspentOutputs contractValidator redeemer
    void $ submitTx tx

endpoints :: AsContractError e => Contract Schema e ()
endpoints = contract

mkSchemaDefinitions ''Schema

$(mkKnownCurrencies [])
