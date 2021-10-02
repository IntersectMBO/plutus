{-# LANGUAGE DataKinds          #-}
{-# LANGUAGE FlexibleContexts   #-}
{-# LANGUAGE FlexibleInstances  #-}
{-# LANGUAGE GADTs              #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell    #-}
{-# LANGUAGE TypeApplications   #-}
{-# LANGUAGE TypeFamilies       #-}
{-# LANGUAGE TypeOperators      #-}
{-# OPTIONS_GHC -fno-warn-name-shadowing #-}
module Spec.ErrorChecking where

import           Control.Monad
import           Data.Row
import           Test.Tasty

import qualified Ledger.Ada                         as Ada
import           Ledger.Address
import           Ledger.Constraints
import           Ledger.Contexts                    (ScriptContext (..))
import           Ledger.Scripts
import           Ledger.Tx
import qualified Ledger.Typed.Scripts               as Scripts hiding (validatorHash)
import           Ledger.Typed.Scripts.Validators    hiding (validatorHash)
import           Plutus.Contract                    as Contract
import           Plutus.Contract.Test               hiding (not)
import           Plutus.Contract.Test.ContractModel
import           Plutus.Trace.Emulator              as Trace
import qualified PlutusTx
import           PlutusTx.IsData.Class
import           PlutusTx.Prelude

import qualified Prelude                            as Haskell

import           Test.QuickCheck                    hiding (Success)
import           Test.Tasty.QuickCheck              hiding (Success)

tests :: TestTree
tests = testGroup "error checking"
  [ testProperty "Normal failures allowed" $ withMaxSuccess 1 prop_FailFalse
  , testProperty "Failure due to head [] not allowed" $ withMaxSuccess 1 $ expectFailure prop_FailHeadNil
  , testProperty "Division by zero not allowed" $ withMaxSuccess 1 $ expectFailure prop_DivZero
  , testProperty "Normal success allowed" $ withMaxSuccess 1 prop_Success ]

-- | Normal failures should be allowed
prop_FailFalse :: Property
prop_FailFalse = checkErrorWhitelist handleSpecs emptyWhitelist (Actions [FailFalse])

-- | Head Nil failure should not be allowed
prop_FailHeadNil :: Property
prop_FailHeadNil = checkErrorWhitelist handleSpecs emptyWhitelist (Actions [FailHeadNil])

-- | Head Nil failure should not be allowed
prop_DivZero :: Property
prop_DivZero = checkErrorWhitelist handleSpecs emptyWhitelist (Actions [DivZero])

-- | Head Nil failure should not be allowed
prop_Success :: Property
prop_Success = checkErrorWhitelist handleSpecs emptyWhitelist (Actions [Success])

data DummyModel = DummyModel deriving Haskell.Show

deriving instance Haskell.Eq (ContractInstanceKey DummyModel w schema err)
deriving instance Haskell.Show (ContractInstanceKey DummyModel w schema err)

instance ContractModel DummyModel where
  data ContractInstanceKey DummyModel w schema err where
    WalletKey :: Wallet -> ContractInstanceKey DummyModel () Schema ContractError

  data Action DummyModel = FailFalse
                         | FailHeadNil
                         | DivZero
                         | Success
                         deriving (Haskell.Eq, Haskell.Show)

  perform handle _ cmd = void $ case cmd of
    FailFalse -> do
      callEndpoint @"failFalse" (handle $ WalletKey w1) ()
      Trace.waitNSlots 2
    FailHeadNil -> do
      callEndpoint @"failHeadNil" (handle $ WalletKey w1) ()
      Trace.waitNSlots 2
    DivZero -> do
      callEndpoint @"divZero" (handle $ WalletKey w1) ()
      Trace.waitNSlots 2
    Success -> do
      callEndpoint @"success" (handle $ WalletKey w1) ()
      Trace.waitNSlots 2

  initialState = DummyModel

  nextState _ = wait 2

  arbitraryAction _ = elements [FailFalse, FailHeadNil, DivZero, Success]

data Validators
instance Scripts.ValidatorTypes Validators where
    type instance RedeemerType Validators = Integer
    type instance DatumType Validators = ()

type Schema = Endpoint "failFalse" ()
            .\/ Endpoint "failHeadNil" ()
            .\/ Endpoint "divZero" ()
            .\/ Endpoint "success" ()

handleSpecs :: [ContractInstanceSpec DummyModel]
handleSpecs = [ContractInstanceSpec (WalletKey w1) w1 contract]

contract :: Contract () Schema ContractError ()
contract = selectList [failFalseC, failHeadNilC, divZeroC, successC] >> contract
  where
    run validator = void $ do
      let addr = scriptAddress (validatorScript validator)
          hash = validatorHash (validatorScript validator)
          tx = mustPayToOtherScript hash (Datum $ toBuiltinData ()) (Ada.lovelaceValueOf 1)
      r <- submitTx tx
      awaitTxConfirmed (txId r)
      utxos <- utxosAt addr
      let tx' = collectFromScript utxos 0
      submitTxConstraintsSpending validator utxos tx'

    failFalseC = endpoint @"failFalse" $ \ _ -> do
      run v_failFalse

    failHeadNilC = endpoint @"failHeadNil" $ \ _ -> do
      run v_failHeadNil

    divZeroC = endpoint @"divZero" $ \ _ -> do
      run v_divZero

    successC = endpoint @"success" $ \ _ -> do
      run v_success

{-# INLINEABLE failFalse #-}
failFalse :: () -> Integer -> ScriptContext -> Bool
failFalse _ _ _ = False

v_failFalse :: Scripts.TypedValidator Validators
v_failFalse = Scripts.mkTypedValidator @Validators
    $$(PlutusTx.compile [|| failFalse ||])
    $$(PlutusTx.compile [|| wrap ||])
    where
        wrap = Scripts.wrapValidator

{-# INLINEABLE failHeadNil #-}
failHeadNil :: () -> Integer -> ScriptContext -> Bool
failHeadNil _ _ _ = head []

v_failHeadNil :: Scripts.TypedValidator Validators
v_failHeadNil = Scripts.mkTypedValidator @Validators
    $$(PlutusTx.compile [|| failHeadNil ||])
    $$(PlutusTx.compile [|| wrap ||])
    where
        wrap = Scripts.wrapValidator

{-# INLINEABLE divZero #-}
divZero :: () -> Integer -> ScriptContext -> Bool
divZero _ _ _ = (10 `divide` 0) > 5

v_divZero :: Scripts.TypedValidator Validators
v_divZero = Scripts.mkTypedValidator @Validators
    $$(PlutusTx.compile [|| divZero ||])
    $$(PlutusTx.compile [|| wrap ||])
    where
        wrap = Scripts.wrapValidator

{-# INLINEABLE success #-}
success :: () -> Integer -> ScriptContext -> Bool
success _ _ _ = True

v_success :: Scripts.TypedValidator Validators
v_success = Scripts.mkTypedValidator @Validators
    $$(PlutusTx.compile [|| success ||])
    $$(PlutusTx.compile [|| wrap ||])
    where
        wrap = Scripts.wrapValidator
