{-# LANGUAGE DataKinds          #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleContexts   #-}
{-# LANGUAGE OverloadedStrings  #-}
{-# LANGUAGE RankNTypes         #-}
{-# LANGUAGE TypeApplications   #-}
{-# LANGUAGE TypeFamilies       #-}
module Main(main, marloweTest) where

import           Control.Monad                       (guard, void)
import qualified Data.Aeson                          as JSON
import qualified Data.Aeson.Types                    as JSON
import qualified Data.Map                            as Map
import           Data.Maybe                          (listToMaybe)
import qualified Language.Marlowe.Client             as Marlowe
import           Language.Marlowe.Semantics          (Action (..), Case (..), Contract (..), MarloweParams, Party (..),
                                                      Payee (..), Value (..))
import qualified Language.Marlowe.Semantics          as Marlowe
import           Language.Marlowe.Util               (ada)
import           Ledger                              (PubKeyHash, Slot, pubKeyHash)
import qualified Ledger.Value                        as Val
import           MarloweContract                     (MarloweContract (..), handlers)
import           Plutus.PAB.Effects.Contract.Builtin (Builtin)
import qualified Plutus.PAB.Effects.Contract.Builtin as Builtin
import           Plutus.PAB.Run                      (runWith)
import qualified Plutus.PAB.Simulator                as Simulator
import qualified Plutus.PAB.Webserver.Server         as PAB.Server
import qualified PlutusTx.AssocMap                   as AssocMap

main :: IO ()
main = runWith (Builtin.handleBuiltin @MarloweContract)

marloweTest :: IO ()
marloweTest = void $ Simulator.runSimulationWith handlers $ do
    Simulator.logString @(Builtin MarloweContract) "Starting marlowe PAB webserver on port 8080. Press enter to exit."
    shutdown <- PAB.Server.startServerDebug
    (newWallet, newPubKey) <- Simulator.addWallet @(Builtin MarloweContract)
    Simulator.logString @(Builtin MarloweContract) "Created new wallet"
    walletCompanionId <- Simulator.activateContract newWallet WalletCompanion
    Simulator.logString @(Builtin MarloweContract) "Activated companion contract"
    marloweContractId <- Simulator.activateContract newWallet MarloweApp
    Simulator.logString @(Builtin MarloweContract) "Activated marlowe contract"

    void $ Simulator.waitNSlots 10

    let args = let h = pubKeyHash newPubKey in createArgs h h
    void $ Simulator.callEndpointOnInstance marloweContractId "create" args

    followerId <- Simulator.activateContract newWallet MarloweFollower
    Simulator.logString @(Builtin MarloweContract) "Activated marlowe follower"

    mp <- Simulator.waitForState @(Builtin MarloweContract) extractMarloweParams walletCompanionId
    Simulator.logString @(Builtin MarloweContract) $ "Found marlowe params: " <> show mp

    _ <- Simulator.waitForEndpoint followerId "follow"
    Simulator.logString @(Builtin MarloweContract) $ "Calling endpoint on marlowe follow"
    _ <- Simulator.callEndpointOnInstance followerId "follow" mp

    followState <- Simulator.waitForState @(Builtin MarloweContract) extractFollowState followerId

    Simulator.logString @(Builtin MarloweContract) $ "Follow state: " <> show followState

    shutdown

extractMarloweParams :: JSON.Value -> Maybe MarloweParams
extractMarloweParams vl = do
    (Marlowe.CompanionState s) <- either (const Nothing) Just (JSON.parseEither JSON.parseJSON vl)
    (params, _) <- listToMaybe $ Map.toList s
    pure params

extractFollowState :: JSON.Value -> Maybe Marlowe.ContractHistory
extractFollowState vl = do
    s <- either (const Nothing) Just (JSON.parseEither JSON.parseJSON vl)
    guard (not $ Marlowe.isEmpty s)
    pure s

createArgs :: PubKeyHash -> PubKeyHash -> (AssocMap.Map Val.TokenName PubKeyHash, Marlowe.Contract)
createArgs investor issuer = (tokenNames, zcb) where
    tokenNames = AssocMap.fromList [("Investor", investor), ("Issuer", issuer)]
    issuerAcc = Role "Issuer"
    investorAcc = Role "Investor"
    zcb = When
            [ Case
                (Deposit issuerAcc issuerAcc ada (Constant 850))
                (Pay issuerAcc (Account investorAcc) ada (Constant 850)
                    (When
                        [ Case (Deposit issuerAcc investorAcc ada (Constant 1000)) Close
                        ] (26936589 :: Slot) Close
                    )
                )
            ]
            (26936589 :: Slot) Close
