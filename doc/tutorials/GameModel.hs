{-# LANGUAGE DataKinds          #-}
{-# LANGUAGE DeriveFunctor      #-}
{-# LANGUAGE FlexibleContexts   #-}
{-# LANGUAGE FlexibleInstances  #-}
{-# LANGUAGE GADTs              #-}
{-# LANGUAGE OverloadedStrings  #-}
{-# LANGUAGE RankNTypes         #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell    #-}
{-# LANGUAGE TypeApplications   #-}
{-# LANGUAGE TypeFamilies       #-}

{-# OPTIONS_GHC -Wno-name-shadowing -Wno-unused-matches -Wno-unused-do-bind -Wno-unused-local-binds #-}

module GameModel where

import           Control.Applicative
import           Control.Lens                       hiding (elements)
import           Control.Monad
import           System.Random

-- START import Log
import           Control.Monad.Freer.Extras.Log     (LogLevel (..))
-- END import Log

import           Data.Maybe
import           Test.QuickCheck

-- START import Contract.Test
import           Plutus.Contract.Test
-- END import Contract.Test

-- START import ContractModel
import           Plutus.Contract.Test.ContractModel
-- END import ContractModel

import           Plutus.Contract.Test.ContractModel as ContractModel

-- START import Game
import           Plutus.Contracts.GameStateMachine  as G
-- END import Game

-- START import Ada
import qualified Ledger.Ada                         as Ada
import           Ledger.Value
-- END import Ada

-- START import Scripts
import qualified Ledger.Typed.Scripts               as Scripts
-- END import Scripts

-- START import Emulator
import           Plutus.Trace.Emulator              as Trace
-- END import Emulator

-- * QuickCheck model

-- START GameModel
data GameModel = GameModel
    { _gameValue     :: Integer
    , _hasToken      :: Maybe Wallet
    , _currentSecret :: String }
  deriving (Show)

makeLenses 'GameModel
-- END GameModel

deriving instance Eq (ContractInstanceKey GameModel schema err)
deriving instance Show (ContractInstanceKey GameModel schema err)

-- START instance ContractModel and Action type
instance ContractModel GameModel where

    data Action GameModel = Lock      Wallet String Integer
                          | Guess     Wallet String String Integer
                          | GiveToken Wallet
        deriving (Eq, Show)
-- END instance ContractModel and Action type

-- START ContractInstanceKey
    data ContractInstanceKey GameModel schema err where
        WalletKey :: Wallet -> ContractInstanceKey GameModel G.GameStateMachineSchema G.GameError
-- END ContractInstanceKey

-- START initialState
    initialState = GameModel
        { _gameValue     = 0
        , _hasToken      = Nothing
        , _currentSecret = ""
        }
-- END initialState

-- START perform
    perform handle s cmd = case cmd of
        Lock w new val -> do
            callEndpoint @"lock" (handle $ WalletKey w)
                         LockArgs{ lockArgsSecret = new
                                 , lockArgsValue = Ada.lovelaceValueOf val }
            delay 2
        Guess w old new val -> do
            callEndpoint @"guess" (handle $ WalletKey w)
                GuessArgs{ guessArgsOldSecret     = old
                         , guessArgsNewSecret     = new
                         , guessArgsValueTakenOut = Ada.lovelaceValueOf val }
            delay 1
        GiveToken w' -> do
            let w = fromJust (s ^. contractState . hasToken)
            payToWallet w w' gameTokenVal
            delay 1
-- END perform

    -- 'nextState' descibes how each command affects the state of the model
    nextState (Lock w secret val) = do
        wasUnlocked <- (Nothing ==) <$> viewContractState hasToken
        when wasUnlocked $ do
          hasToken      $= Just w
          currentSecret $= secret
          gameValue     $= val
          forge gameTokenVal
          deposit  w gameTokenVal
        withdraw w $ Ada.lovelaceValueOf val
        wait 2

-- START nextState Guess
    nextState (Guess w old new val) = do
        correctGuess <- (old ==)    <$> viewContractState currentSecret
        holdsToken   <- (Just w ==) <$> viewContractState hasToken
        enoughAda    <- (val <=)    <$> viewContractState gameValue
        when (correctGuess && holdsToken && enoughAda) $ do
            currentSecret $= new
            gameValue     $~ subtract val
            deposit w $ Ada.lovelaceValueOf val
        wait 1
-- END nextState Guess

    nextState (GiveToken w) = do
        w0 <- fromJust <$> viewContractState hasToken
        transfer w0 w gameTokenVal
        hasToken $= Just w
        wait 1

-- START arbitraryAction
    arbitraryAction s = oneof $
        [ Lock      <$> genWallet <*> genGuess <*> genValue ] ++
        [ frequency $
          [ (10, Guess w   <$> genGuess  <*> genGuess <*> choose (0, val))
          | Just w <- [tok] ] ++
          [ (1, Guess <$> genWallet <*> genGuess <*> genGuess <*> genValue) ] ] ++
        [ GiveToken <$> genWallet ]
        where
            tok = s ^. contractState . hasToken
            val = s ^. contractState . gameValue
-- END arbitraryAction

-- START precondition
    precondition s cmd = case cmd of
            Lock _ _ v    -> tok == Nothing
            Guess w _ _ v -> tok == Just w && v <= val
            GiveToken w   -> tok /= Nothing
        where
            tok = s ^. contractState . hasToken
            val = s ^. contractState . gameValue
-- END precondition

-- START shrinkAction
    shrinkAction _s (Lock w secret val) =
        [Lock w' secret val | w' <- shrinkWallet w] ++
        [Lock w secret val' | val' <- shrink val]
    shrinkAction _s (GiveToken w) =
        [GiveToken w' | w' <- shrinkWallet w]
    shrinkAction _s (Guess w old new val) =
        [Guess w' old new val | w' <- shrinkWallet w] ++
        [Guess w old new val' | val' <- shrink val]
-- END shrinkAction

-- START monitoring
    monitoring (s, _) (Guess w guess new v) =
        tabulate "Guesses" [if guess == secret then "Right" else "Wrong"]
        where secret = s ^. contractState . currentSecret
    monitoring _ _ = id
-- END monitoring

-- START instanceSpec
instanceSpec :: [ContractInstanceSpec GameModel]
instanceSpec = [ ContractInstanceSpec (WalletKey w) w G.contract | w <- wallets ]
-- END instanceSpec

-- START prop_Game
prop_Game :: Actions GameModel -> Property
prop_Game actions = propRunActions_ instanceSpec actions
-- END prop_Game

-- START propGame'
propGame' :: LogLevel -> Actions GameModel -> Property
propGame' l s = propRunActionsWithOptions
                    (set minLogLevel l defaultCheckOptions)
                    instanceSpec
                    (\ _ -> pure True)
                    s
-- END propGame'

-- START Generators
genWallet :: Gen Wallet
genWallet = elements wallets

genGuess :: Gen String
genGuess = elements ["hello", "secret", "hunter2", "*******"]

genValue :: Gen Integer
genValue = getNonNegative <$> arbitrary
-- END Generators

-- START shrinkWallet
shrinkWallet :: Wallet -> [Wallet]
shrinkWallet w = [w' | w' <- wallets, w' < w]
-- END shrinkWallet

guesses :: [String]
guesses = ["hello", "secret", "hunter2", "*******"]

-- START delay
delay :: Int -> EmulatorTrace ()
delay n = void $ waitNSlots (fromIntegral n)
-- END delay

-- Dynamic Logic ----------------------------------------------------------

prop_UnitTest :: Property
prop_UnitTest = withMaxSuccess 1 $ forAllDL unitTest prop_Game

-- START propDL
propDL :: DL GameModel () -> Property
propDL dl = forAllDL dl prop_Game
-- END propDL

-- START unitTest
unitTest :: DL GameModel ()
unitTest = do
    val <- forAllQ $ chooseQ (3, 20)
    action $ Lock w1 "hello" val
    action $ GiveToken w2
    action $ Guess w2 "hello" "new secret" 3
-- END unitTest

-- START badUnitTest
badUnitTest :: DLTest GameModel
badUnitTest =
    BadPrecondition
      [Witness (1 :: Integer),
       Do $ Lock (Wallet 1) "hello" 1,
       Do $ GiveToken (Wallet 2)]
      [Action (Guess (Wallet 2) "hello" "new secret" 3)]
      (GameModel {_gameValue = 1, _hasToken = Just (Wallet 2), _currentSecret = "hello"})
-- END badUnitTest

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

-- START noLockedFunds
noLockedFunds :: DL GameModel ()
noLockedFunds = do
    (w0, funds, pass) <- forAllQ (elementsQ wallets, chooseQ (1, 10000), elementsQ guesses)
    action $ Lock w0 pass funds
    anyActions_
    w      <- forAllQ $ elementsQ wallets
    secret <- viewContractState currentSecret
    val    <- viewContractState gameValue
    when (val > 0) $ do
        monitor $ label "Unlocking funds"
        action $ GiveToken w
        action $ Guess w secret "" val
    assertModel "Locked funds should be zero" $ isZero . lockedValue
-- END noLockedFunds

-- | Check that we can always get the money out of the guessing game (by guessing correctly).
prop_NoLockedFunds :: Property
prop_NoLockedFunds = forAllDL noLockedFunds prop_Game

-- | Wallets and game token.

-- START wallets
w1, w2, w3 :: Wallet
w1 = Wallet 1
w2 = Wallet 2
w3 = Wallet 3

wallets :: [Wallet]
wallets = [w1, w2, w3]
-- END wallets

-- START gameTokenVal
gameTokenVal :: Value
gameTokenVal =
    let sym = Scripts.monetaryPolicyHash G.scriptInstance
    in G.token sym "guess"
-- END gameTokenVal

-- START testLock v1
testLock :: Property
testLock = prop_Game $ Actions [Lock (Wallet 1) "hunter2" 0]
-- END testLock v1

testLockWithMaxSuccess :: ()
testLockWithMaxSuccess = ()
 where
-- START testLock withMaxSuccess
 testLock :: Property
 testLock = withMaxSuccess 1 . prop_Game $ Actions [Lock (Wallet 1) "hunter2" 0]
-- END testLock withMaxSuccess

-- START testDoubleLock
testDoubleLock :: Property
testDoubleLock = prop_Game $
  Actions
    [Lock (Wallet 1) "*******" 0,
     Lock (Wallet 1) "secret" 0]
-- END testDoubleLock

anyActionsDef :: ()
anyActionsDef = ()
 where
-- START anyActions
 anyActions :: Int -> DL s ()
 anyActions n = stopping
            <|> weight (1 / fromIntegral n)
            <|> (anyAction >> anyActions n)
-- END anyActions

-- Code for preliminary versions

v1_model :: ()
v1_model = ()
  where
    arbitraryAction :: ModelState GameModel -> Gen (Action GameModel)
-- START arbitraryAction v1
    arbitraryAction s = oneof $
        [ Lock      <$> genWallet <*> genGuess <*> genValue              ] ++
        [ Guess     <$> genWallet <*> genGuess <*> genGuess <*> genValue ] ++
        [ GiveToken <$> genWallet                                        ]
-- END arbitraryAction v1

    nextState :: Action GameModel -> Spec GameModel ()
-- START nextState Lock v1
    nextState (Lock w secret val) = do
        hasToken      $= Just w
        currentSecret $= secret
        gameValue     $= val
        forge gameTokenVal
        deposit  w gameTokenVal
        withdraw w $ Ada.lovelaceValueOf val
-- END nextState Lock v1
-- START nextState Guess v1
    nextState (Guess w old new val) = do
        correctGuess <- (old ==)    <$> viewContractState currentSecret
        holdsToken   <- (Just w ==) <$> viewContractState hasToken
        enoughAda    <- (val <=)    <$> viewContractState gameValue
        when (correctGuess && holdsToken && enoughAda) $ do
            currentSecret $= new
            gameValue     $~ subtract val
            deposit w $ Ada.lovelaceValueOf val
-- END nextState Guess v1
-- START nextState GiveToken v1
    nextState (GiveToken w) = do
        w0 <- fromJust <$> viewContractState hasToken
        transfer w0 w gameTokenVal
        hasToken $= Just w
-- END nextState GiveToken v1

    precondition :: ModelState GameModel -> Action GameModel -> Bool
-- START precondition v1
    precondition s (GiveToken _) = tok /= Nothing
        where
            tok = s ^. contractState . hasToken
    precondition s _             = True
-- END precondition v1

    perform :: HandleFun GameModel -> ModelState GameModel -> Action GameModel -> EmulatorTrace ()
-- START perform v1
    perform handle s cmd = case cmd of
        Lock w new val -> do
            callEndpoint @"lock" (handle $ WalletKey w)
                         LockArgs{ lockArgsSecret = new
                                 , lockArgsValue = Ada.lovelaceValueOf val}
        Guess w old new val -> do
            callEndpoint @"guess" (handle $ WalletKey w)
                GuessArgs{ guessArgsOldSecret = old
                         , guessArgsNewSecret = new
                         , guessArgsValueTakenOut = Ada.lovelaceValueOf val}
        GiveToken w' -> do
            let w = fromJust (s ^. contractState . hasToken)
            payToWallet w w' gameTokenVal
            return ()
-- END perform v1

v2_model :: ()
v2_model = ()
  where
    nextState :: Action GameModel -> Spec GameModel ()
-- START nextState Lock v2
    nextState (Lock w secret val) = do
        hasToken      $= Just w
        currentSecret $= secret
        gameValue     $= val
        forge gameTokenVal
        deposit  w gameTokenVal
        withdraw w $ Ada.lovelaceValueOf val
        wait 2
-- END nextState Lock v2
-- START nextState Guess partial
    nextState (Guess w old new val) = do
        correctGuess <- (old ==)    <$> viewContractState currentSecret
        -- ...
-- END nextState Guess partial
        return ()
    nextState _ = return ()

    precondition :: ModelState GameModel -> Action GameModel -> Bool
-- START precondition v2
    precondition s cmd = case cmd of
            Lock _ _ _    -> tok == Nothing
            Guess _ _ _ _ -> True
            GiveToken _   -> tok /= Nothing
        where
            tok = s ^. contractState . hasToken
-- END precondition v2

    arbitraryAction :: ModelState GameModel -> Gen (Action GameModel)
-- START arbitaryAction v2
    arbitraryAction s = oneof $
        [ Lock      <$> genWallet <*> genGuess <*> genValue ] ++
        [ Guess w   <$> genGuess  <*> genGuess <*> choose (0, val)
        | Just w <- [tok] ] ++
        [ GiveToken <$> genWallet ]
        where
            tok = s ^. contractState . hasToken
            val = s ^. contractState . gameValue
-- END arbitaryAction v2

v3_model :: ()
v3_model = ()
  where
    precondition :: ModelState GameModel -> Action GameModel -> Bool
-- START precondition v3
    precondition s cmd = case cmd of
            Lock _ _ _    -> tok == Nothing
            Guess w _ _ _ -> tok == Just w
            GiveToken _   -> tok /= Nothing
        where
            tok = s ^. contractState . hasToken
-- END precondition v3

unitTest_v1 :: ()
unitTest_v1 = ()
 where
-- START unitTest v1
 unitTest :: DL GameModel ()
 unitTest = do
     action $ Lock w1 "hello" 10
     action $ GiveToken w2
     action $ Guess w2 "hello" "new secret" 3
-- END unitTest v1

unitTest_v2 :: ()
unitTest_v2 = ()
 where
-- START unitTest v2
 unitTest :: DL GameModel ()
 unitTest = do
     val <- forAllQ $ chooseQ (1, 20)
     action $ Lock w1 "hello" val
     action $ GiveToken w2
     action $ Guess w2 "hello" "new secret" 3
-- END unitTest v2

noLockedFunds_v1 :: ()
noLockedFunds_v1 = ()
 where
-- START noLockedFunds v1
 noLockedFunds :: DL GameModel ()
 noLockedFunds = do
     anyActions_
     assertModel "Locked funds should be zero" $ isZero . lockedValue
-- END noLockedFunds v1

noLockedFunds_v2 :: ()
noLockedFunds_v2 = ()
 where
-- START noLockedFunds v2
 noLockedFunds :: DL GameModel ()
 noLockedFunds = do
     anyActions_
     w      <- forAllQ $ elementsQ wallets
     secret <- viewContractState currentSecret
     val    <- viewContractState gameValue
     action $ Guess w "" secret val
     assertModel "Locked funds should be zero" $ isZero . lockedValue
-- END noLockedFunds v2

noLockedFunds_v3 :: ()
noLockedFunds_v3 = ()
 where
-- START noLockedFunds v3
 noLockedFunds :: DL GameModel ()
 noLockedFunds = do
     anyActions_
     w      <- forAllQ $ elementsQ wallets
     secret <- viewContractState currentSecret
     val    <- viewContractState gameValue
     when (val > 0) $ do
         action $ Guess w "" secret val
     assertModel "Locked funds should be zero" $ isZero . lockedValue
-- END noLockedFunds v3

noLockedFunds_v4 :: ()
noLockedFunds_v4 = ()
 where
-- START noLockedFunds v4
 noLockedFunds :: DL GameModel ()
 noLockedFunds = do
     anyActions_
     w      <- forAllQ $ elementsQ wallets
     secret <- viewContractState currentSecret
     val    <- viewContractState gameValue
     when (val > 0) $ do
         action $ GiveToken w
         action $ Guess w "" secret val
     assertModel "Locked funds should be zero" $ isZero . lockedValue
-- END noLockedFunds v4

noLockedFunds_v5 :: ()
noLockedFunds_v5 = ()
 where
-- START noLockedFunds v5
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
-- END noLockedFunds v5

typeSignatures :: forall state. ContractModel state => state -> state
typeSignatures = id
 where
-- START nextState type
 nextState :: Action state -> Spec state ()
-- END nextState type
 nextState = ContractModel.nextState
-- START precondition type
 precondition :: ModelState state -> Action state -> Bool
-- END precondition type
 precondition = ContractModel.precondition
-- START perform type
 perform :: HandleFun state -> ModelState state -> Action state -> EmulatorTrace ()
-- END perform type
 perform = ContractModel.perform
-- START shrinkAction type
 shrinkAction :: ModelState state -> Action state -> [Action state]
-- END shrinkAction type
 shrinkAction = ContractModel.shrinkAction
-- START monitoring type
 monitoring :: (ModelState state, ModelState state) -> Action state -> Property -> Property
-- END monitoring type
 monitoring = ContractModel.monitoring
-- START chooseQ type
 chooseQ :: (Arbitrary a, Random a, Ord a) => (a, a) -> Quantification a
-- END chooseQ type
 chooseQ = ContractModel.chooseQ

