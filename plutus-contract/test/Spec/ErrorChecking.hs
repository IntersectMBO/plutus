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
import           PlutusTx.ErrorCodes
import           PlutusTx.IsData.Class
import           PlutusTx.Prelude

import qualified Prelude                            as Haskell

import           Test.QuickCheck                    hiding (Success)
import           Test.Tasty.HUnit
import           Test.Tasty.QuickCheck              hiding (Success)

tests :: TestTree
tests = testGroup "error checking"
  [ testProperty "Normal failures allowed" $ withMaxSuccess 1 prop_FailFalse
  , testProperty "Failure due to head [] not allowed" $ withMaxSuccess 1 $ expectFailure prop_FailHeadNil
  , testProperty "Division by zero not allowed" $ withMaxSuccess 1 $ expectFailure prop_DivZero
  , testProperty "Can't trick division by zero check using trace" $ withMaxSuccess 1 $ expectFailure prop_DivZero_t
  , testProperty "Normal success allowed" $ withMaxSuccess 1 prop_Success
  , testCase "Check defaultWhitelist is ok" $ assertBool "whitelistOk defaultWhitelist" $ whitelistOk defaultWhitelist ]

-- | Normal failures should be allowed
prop_FailFalse :: Property
prop_FailFalse = checkErrorWhitelist handleSpecs defaultWhitelist (Actions [FailFalse])

-- | Head Nil failure should not be allowed
prop_FailHeadNil :: Property
prop_FailHeadNil = checkErrorWhitelist handleSpecs defaultWhitelist (Actions [FailHeadNil])

-- | Division by zero failure should not be allowed
prop_DivZero :: Property
prop_DivZero = checkErrorWhitelist handleSpecs defaultWhitelist (Actions [DivZero])

-- | Division by zero failure should not be allowed (tracing before the failure).
prop_DivZero_t :: Property
prop_DivZero_t = checkErrorWhitelist handleSpecs defaultWhitelist (Actions [DivZero_t])

-- | Successful validation should be allowed
prop_Success :: Property
prop_Success = checkErrorWhitelist handleSpecs defaultWhitelist (Actions [Success])

-- | This QuickCheck model only provides an interface to the validators used in this
-- test that are convenient for testing them in isolation.
data DummyModel = DummyModel deriving Haskell.Show

deriving instance Haskell.Eq (ContractInstanceKey DummyModel w schema err)
deriving instance Haskell.Show (ContractInstanceKey DummyModel w schema err)

instance ContractModel DummyModel where
  data ContractInstanceKey DummyModel w schema err where
    WalletKey :: Wallet -> ContractInstanceKey DummyModel () Schema ContractError

  data Action DummyModel = FailFalse
                         | FailHeadNil
                         | DivZero
                         | DivZero_t    -- Trace before dividing by zero
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
    DivZero_t -> do
      callEndpoint @"divZero_t" (handle $ WalletKey w1) ()
      Trace.waitNSlots 2
    Success -> do
      callEndpoint @"success" (handle $ WalletKey w1) ()
      Trace.waitNSlots 2

  initialState = DummyModel

  nextState _ = wait 2

  arbitraryAction _ = elements [FailFalse, FailHeadNil, DivZero, DivZero_t, Success]

data Validators
instance Scripts.ValidatorTypes Validators where
    type instance RedeemerType Validators = Integer
    type instance DatumType Validators = ()

type Schema = Endpoint "failFalse" ()
            .\/ Endpoint "failHeadNil" ()
            .\/ Endpoint "divZero" ()
            .\/ Endpoint "divZero_t" ()
            .\/ Endpoint "success" ()

handleSpecs :: [ContractInstanceSpec DummyModel]
handleSpecs = [ContractInstanceSpec (WalletKey w1) w1 contract]

-- | For each endpoint in the schema: pay to the corresponding validator
-- and then spend that UTxO
contract :: Contract () Schema ContractError ()
contract = selectList [failFalseC, failHeadNilC, divZeroC, divZeroTraceC, successC]
  where
    run validator = void $ do
      let addr = scriptAddress (validatorScript validator)
          hash = validatorHash (validatorScript validator)
          tx = mustPayToOtherScript hash (Datum $ toBuiltinData ()) (Ada.lovelaceValueOf 1)
      r <- submitTx tx
      awaitTxConfirmed (getCardanoTxId r)
      utxos <- utxosAt addr
      let tx' = collectFromScript utxos 0
      submitTxConstraintsSpending validator utxos tx'

    failFalseC = endpoint @"failFalse" $ \ _ -> do
      run v_failFalse

    failHeadNilC = endpoint @"failHeadNil" $ \ _ -> do
      run v_failHeadNil

    divZeroC = endpoint @"divZero" $ \ _ -> do
      run v_divZero

    divZeroTraceC = endpoint @"divZero_t" $ \ _ -> do
      run v_divZero_t

    successC = endpoint @"success" $ \ _ -> do
      run v_success

-- | Always fail "benignly"
{-# INLINEABLE failFalse #-}
failFalse :: () -> Integer -> ScriptContext -> Bool
failFalse _ _ _ = False

v_failFalse :: Scripts.TypedValidator Validators
v_failFalse = Scripts.mkTypedValidator @Validators
    $$(PlutusTx.compile [|| failFalse ||])
    $$(PlutusTx.compile [|| wrap ||])
    where
        wrap = Scripts.wrapValidator

-- | Always fail due to a partial function
{-# INLINEABLE failHeadNil #-}
failHeadNil :: () -> Integer -> ScriptContext -> Bool
failHeadNil _ _ _ = head []

v_failHeadNil :: Scripts.TypedValidator Validators
v_failHeadNil = Scripts.mkTypedValidator @Validators
    $$(PlutusTx.compile [|| failHeadNil ||])
    $$(PlutusTx.compile [|| wrap ||])
    where
        wrap = Scripts.wrapValidator

-- | Always fail with a division by zero error
{-# INLINEABLE divZero #-}
divZero :: () -> Integer -> ScriptContext -> Bool
divZero _ _ _ = (10 `divide` 0) > 5

v_divZero :: Scripts.TypedValidator Validators
v_divZero = Scripts.mkTypedValidator @Validators
    $$(PlutusTx.compile [|| divZero ||])
    $$(PlutusTx.compile [|| wrap ||])
    where
        wrap = Scripts.wrapValidator

{-# INLINEABLE divZero_t #-}
divZero_t :: () -> Integer -> ScriptContext -> Bool
divZero_t _ _ _ = trace checkHasFailedError False || (10 `divide` 0) > 5
                  -- Trying to cheat by tracing a whitelisted error before failing.
                  -- Currently this tricks the whitelist check.

v_divZero_t :: Scripts.TypedValidator Validators
v_divZero_t = Scripts.mkTypedValidator @Validators
    $$(PlutusTx.compile [|| divZero_t ||])
    $$(PlutusTx.compile [|| wrap ||])
    where
        wrap = Scripts.wrapValidator

-- | Always succeed
{-# INLINEABLE success #-}
success :: () -> Integer -> ScriptContext -> Bool
success _ _ _ = True

v_success :: Scripts.TypedValidator Validators
v_success = Scripts.mkTypedValidator @Validators
    $$(PlutusTx.compile [|| success ||])
    $$(PlutusTx.compile [|| wrap ||])
    where
        wrap = Scripts.wrapValidator
