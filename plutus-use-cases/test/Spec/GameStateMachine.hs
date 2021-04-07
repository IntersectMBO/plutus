{-# LANGUAGE DataKinds            #-}
{-# LANGUAGE DeriveFunctor        #-}
{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE GADTs                #-}
{-# LANGUAGE MonoLocalBinds       #-}
{-# LANGUAGE MultiWayIf           #-}
{-# LANGUAGE OverloadedStrings    #-}
{-# LANGUAGE RankNTypes           #-}
{-# LANGUAGE ScopedTypeVariables  #-}
{-# LANGUAGE StandaloneDeriving   #-}
{-# LANGUAGE TemplateHaskell      #-}
{-# LANGUAGE TypeApplications     #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE UndecidableInstances #-}
module Spec.GameStateMachine
  ( tests, successTrace, successTrace2, failTrace
  , prop_Game, propGame'
  , prop_NoLockedFunds
  ) where

import           Control.Lens
import           Control.Monad
import           Control.Monad.Freer.Extras.Log     (LogLevel (..))
import           Data.Maybe
import           Test.QuickCheck                    as QC hiding ((.&&.))
import           Test.Tasty                         hiding (after)
import qualified Test.Tasty.HUnit                   as HUnit
import           Test.Tasty.QuickCheck              (testProperty)

import qualified Spec.Lib                           as Lib

import qualified Ledger.Ada                         as Ada
import qualified Ledger.Typed.Scripts               as Scripts
import           Ledger.Value                       (Value, isZero)
import           Plutus.Contract.Test               hiding (not)
import           Plutus.Contract.Test.ContractModel
import           Plutus.Contracts.GameStateMachine  as G
import           Plutus.Trace.Emulator              as Trace
import qualified PlutusTx                           as PlutusTx

-- * QuickCheck model

data GameModel = GameModel
    { _gameValue     :: Integer
    , _hasToken      :: Maybe Wallet
    , _currentSecret :: String }
    deriving (Show)

makeLenses 'GameModel

deriving instance Eq (ContractInstanceKey GameModel w schema err)
deriving instance Show (ContractInstanceKey GameModel w schema err)

instance ContractModel GameModel where

    data ContractInstanceKey GameModel w schema err where
        WalletKey :: Wallet -> ContractInstanceKey GameModel () GameStateMachineSchema GameError

    -- The commands available to a test case
    data Action GameModel = Lock      Wallet String Integer
                          | Guess     Wallet String String Integer
                          | GiveToken Wallet
        deriving (Eq, Show)

    initialState = GameModel
        { _gameValue     = 0
        , _hasToken      = Nothing
        , _currentSecret = ""
        }

    -- 'perform' gets a state, which includes the GameModel state, but also contract handles for the
    -- wallets and what the model thinks the current balances are.
    perform handle s cmd = case cmd of
        Lock w new val -> do
            callEndpoint @"lock" (handle $ WalletKey w)
                         LockArgs{lockArgsSecret = new, lockArgsValue = Ada.lovelaceValueOf val}
            delay 2
        Guess w old new val -> do
            callEndpoint @"guess" (handle $ WalletKey w)
                GuessArgs{ guessArgsOldSecret = old
                         , guessArgsNewSecret = new
                         , guessArgsValueTakenOut = Ada.lovelaceValueOf val}
            delay 1
        GiveToken w' -> do
            let w = fromJust (s ^. contractState . hasToken)
            _ <- payToWallet w w' gameTokenVal
            delay 1

    -- 'nextState' descibes how each command affects the state of the model

    nextState (Lock w secret val) = do
        hasToken      $= Just w
        currentSecret $= secret
        gameValue     $= val
        forge gameTokenVal
        deposit  w gameTokenVal
        withdraw w $ Ada.lovelaceValueOf val
        wait 2

    nextState (Guess w old new val) = do
        correct <- (old ==) <$> viewContractState currentSecret
        when correct $ do
            currentSecret $= new
            gameValue     $~ subtract val
            deposit w $ Ada.lovelaceValueOf val
        wait 1

    nextState (GiveToken w) = do
        w0 <- fromJust <$> viewContractState hasToken
        transfer w0 w gameTokenVal
        hasToken $= Just w
        wait 1

    -- To generate a random test case we need to know how to generate a random
    -- command given the current model state.
    arbitraryAction s = oneof $
        [ Lock      <$> genWallet <*> genGuess <*> genValue ] ++
        [ Guess w   <$> genGuess  <*> genGuess <*> choose (1, val) | Just w <- [tok], val > 0 ] ++
        [ GiveToken <$> genWallet                                  | tok /= Nothing ]
        where
            tok = s ^. contractState . hasToken
            val = s ^. contractState . gameValue

    -- The 'precondition' says when a particular command is allowed.
    precondition s cmd = case cmd of
            Lock _ _ v    -> v > 0 && tok == Nothing
            Guess w _ _ v -> v <= val && tok == Just w
            GiveToken _   -> tok /= Nothing
        where
            tok = s ^. contractState . hasToken
            val = s ^. contractState . gameValue

    shrinkAction _s (Lock w secret val) =
        [Lock w' secret val | w' <- shrinkWallet w] ++
        [Lock w secret val' | val' <- shrink val]
    shrinkAction _s (GiveToken w) =
        [GiveToken w' | w' <- shrinkWallet w]
    shrinkAction _s (Guess w old new val) =
        [Guess w' old new val | w' <- shrinkWallet w] ++
        [Guess w old new val' | val' <- shrink val]

    monitoring _ _ = id

handleSpec :: [ContractInstanceSpec GameModel]
handleSpec = [ ContractInstanceSpec (WalletKey w) w G.contract | w <- wallets ]

-- | The main property. 'propRunActions_' checks that balances match the model after each test.
prop_Game :: Actions GameModel -> Property
prop_Game script = propRunActions_ handleSpec script

propGame' :: LogLevel -> Actions GameModel -> Property
propGame' l s = propRunActionsWithOptions
                    (set minLogLevel l defaultCheckOptions)
                    handleSpec
                    (\ _ -> pure True)
                    s

wallets :: [Wallet]
wallets = [w1, w2, w3]

genWallet :: Gen Wallet
genWallet = QC.elements wallets

shrinkWallet :: Wallet -> [Wallet]
shrinkWallet w = [w' | w' <- wallets, w' < w]

genGuess :: Gen String
genGuess = QC.elements ["hello", "secret", "hunter2", "*******"]

genValue :: Gen Integer
genValue = getPositive <$> arbitrary

delay :: Int -> EmulatorTrace ()
delay n = void $ waitNSlots (fromIntegral n)

-- Dynamic Logic ----------------------------------------------------------

prop_UnitTest :: Property
prop_UnitTest = withMaxSuccess 1 $ forAllDL unitTest prop_Game

unitTest :: DL GameModel ()
unitTest = do
    val <- forAllQ $ chooseQ (5, 20)
    action $ Lock w1 "hello" val
    action $ GiveToken w2
    action $ Guess w2 "hello" "new secret" 3

unitTest2 :: DL GameModel ()
unitTest2 = do
    unitTest
    action $ GiveToken w3
    action $ Guess w3 "new secret" "hello" 4

unitTestFail :: DL GameModel ()
unitTestFail = do
    action $ Lock w1 "hello" 8
    action $ GiveToken w2
    action $ Guess w2 "hola" "new secret" 3

noLockedFunds :: DL GameModel ()
noLockedFunds = do
    anyActions_
    w      <- forAllQ $ elementsQ wallets
    secret <- viewContractState currentSecret
    val    <- viewContractState gameValue
    when (val > 0) $ do
        monitor $ label "Unlocking funds"
        action $ GiveToken w
        action $ Guess w secret "" val
    assertModel "Locked funds should be zero" $ isZero . lockedValue

-- | Check that we can always get the money out of the guessing game (by guessing correctly).
prop_NoLockedFunds :: Property
prop_NoLockedFunds = forAllDL noLockedFunds prop_Game

-- * Unit tests

tests :: TestTree
tests =
    testGroup "game state machine tests"
    [ checkPredicate "run a successful game trace"
        (walletFundsChange w2 (1 `timesFeeAdjust` 3 <> gameTokenVal)
        .&&. valueAtAddress (Scripts.scriptAddress G.scriptInstance) (Ada.lovelaceValueOf 5 ==)
        .&&. walletFundsChange w1 (3 `timesFeeAdjust` (-8)))
        successTrace

    , checkPredicate "run a 2nd successful game trace"
        (walletFundsChange w2 (2 `timesFeeAdjust` 3)
        .&&. valueAtAddress (Scripts.scriptAddress G.scriptInstance) (Ada.lovelaceValueOf 1 ==)
        .&&. walletFundsChange w1 (3 `timesFeeAdjust` (-8))
        .&&. walletFundsChange w3 (1 `timesFeeAdjust` 4 <> gameTokenVal))
        successTrace2

    , checkPredicate "run a failed trace"
        (walletFundsChange w2 gameTokenVal
        .&&. valueAtAddress (Scripts.scriptAddress G.scriptInstance) (Ada.lovelaceValueOf 8 ==)
        .&&. walletFundsChange w1 (3 `timesFeeAdjust` (-8)))
        failTrace

    , Lib.goldenPir "test/Spec/gameStateMachine.pir" $$(PlutusTx.compile [|| mkValidator ||])

    , HUnit.testCase "script size is reasonable"
        (Lib.reasonable (Scripts.validatorScript G.scriptInstance) 49000)

    , testProperty "can always get the funds out" $
        withMaxSuccess 10 prop_NoLockedFunds

    ]

initialVal :: Value
initialVal = Ada.adaValueOf 10

w1 :: Wallet
w1 = Wallet 1

w2 :: Wallet
w2 = Wallet 2

w3 :: Wallet
w3 = Wallet 3

-- | Wallet 1 locks some funds, transfers the token to wallet 2
--   which then makes a correct guess and locks the remaining
--   funds with a new secret
successTrace :: EmulatorTrace ()
successTrace = do
    hdl <- Trace.activateContractWallet w1 G.contract
    Trace.callEndpoint @"lock" hdl LockArgs{lockArgsSecret="hello", lockArgsValue= Ada.lovelaceValueOf 8}
    _ <- Trace.waitNSlots 2
    _ <- Trace.payToWallet w1 w2 gameTokenVal
    _ <- Trace.waitNSlots 1
    hdl2 <- Trace.activateContractWallet w2 G.contract
    Trace.callEndpoint @"guess" hdl2 GuessArgs{guessArgsOldSecret="hello", guessArgsNewSecret="new secret", guessArgsValueTakenOut=Ada.lovelaceValueOf 3}
    void $ Trace.waitNSlots 1

-- | Run 'successTrace', then wallet 2 transfers the token to wallet 3, which
--   makes another correct guess
successTrace2 :: EmulatorTrace ()
successTrace2 = do
    successTrace
    _ <- Trace.payToWallet w2 w3 gameTokenVal
    _ <- Trace.waitNSlots 1
    hdl3 <- Trace.activateContractWallet w3 G.contract
    Trace.callEndpoint @"guess" hdl3 GuessArgs{guessArgsOldSecret="new secret", guessArgsNewSecret="hello", guessArgsValueTakenOut=Ada.lovelaceValueOf 4}
    void $ Trace.waitNSlots 1


-- | Wallet 1 locks some funds, transfers the token to wallet 2
--   which then makes a wrong guess
failTrace :: EmulatorTrace ()
failTrace = do
    hdl <- Trace.activateContractWallet w1 G.contract
    Trace.callEndpoint @"lock" hdl LockArgs{lockArgsSecret="hello", lockArgsValue= Ada.lovelaceValueOf 8}
    _ <- Trace.waitNSlots 2
    _ <- Trace.payToWallet w1 w2 gameTokenVal
    _ <- Trace.waitNSlots 1
    hdl2 <- Trace.activateContractWallet w2 G.contract
    _ <- Trace.callEndpoint @"guess" hdl2 GuessArgs{guessArgsOldSecret="hola", guessArgsNewSecret="new secret", guessArgsValueTakenOut=Ada.lovelaceValueOf 3}
    void $ Trace.waitNSlots 1

gameTokenVal :: Value
gameTokenVal =
    let sym = Scripts.monetaryPolicyHash G.scriptInstance
    in G.token sym "guess"

