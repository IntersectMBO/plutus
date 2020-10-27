{-# LANGUAGE DataKinds         #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications  #-}
module Spec.Prism(tests) where

import           Data.Foldable                                             (traverse_)
import           Language.Plutus.Contract.Test
import           Language.PlutusTx.Lattice
import qualified Ledger.Ada                                                as Ada
import           Ledger.Crypto                                             (pubKeyHash)
import           Ledger.Value                                              (TokenName)
import           Wallet.Emulator.Notify                                    (walletInstanceId)

import           Test.Tasty

import           Language.PlutusTx.Coordination.Contracts.Prism            hiding (credentialManager, mirror)
import qualified Language.PlutusTx.Coordination.Contracts.Prism.Credential as Credential
import           Language.PlutusTx.Coordination.Contracts.Prism.STO        (STOData (..))
import qualified Language.PlutusTx.Coordination.Contracts.Prism.STO        as STO

user, credentialManager, mirror, issuer :: Wallet
user = Wallet 1
mirror = Wallet 2
credentialManager = Wallet 3
issuer = Wallet 4

kyc :: TokenName
kyc = "KYC"

sto :: TokenName
sto = "STO token"

numTokens :: Integer
numTokens = 1000

credential :: Credential
credential =
    Credential
        { credName = kyc
        , credAuthority = CredentialAuthority (pubKeyHash $ walletPubKey mirror)
        }

stoSubscriber :: STOSubscriber
stoSubscriber =
    STOSubscriber
        { wCredential = credential
        , wSTOIssuer = pubKeyHash $ walletPubKey issuer
        , wSTOTokenName = sto
        , wSTOAmount = numTokens
        }

stoData :: STOData
stoData =
    STOData
        { stoIssuer = pubKeyHash $ walletPubKey issuer
        , stoTokenName = sto
        , stoCredentialToken = Credential.token credential
        }

tests :: TestTree
tests = testGroup "PRISM"
    [ checkPredicate "withdraw"
        contract
        (assertDone user (const True) ""
        /\ walletFundsChange issuer (Ada.lovelaceValueOf numTokens)
        /\ walletFundsChange user (Ada.lovelaceValueOf (negate numTokens) <> STO.coins stoData numTokens)
        )
        (callEndpoint @"role" user UnlockSTO
        >> callEndpoint @"role" mirror Mirror
        >> callEndpoint @"role" credentialManager CredMan
        >> handleAll

        -- issue a KYC credential to a user
        >> callEndpoint @"issue" mirror CredentialOwnerReference{coTokenName=kyc, coOwner=user}
        >> handleBlockchainEvents mirror
        >> addBlocks 1
        >> handleAll
        >> addBlocks 1
        >> handleAll

        -- participate in STO presenting the token
        >> callEndpoint @"sto" user stoSubscriber
        >> handleBlockchainEvents user
        >> callEndpoint @"credential manager" user (walletInstanceId credentialManager)
        >> handleBlockchainEvents user
        >> handleBlockchainEvents credentialManager
        >> handleBlockchainEvents user
        >> addBlocks 1
        >> handleAll
        >> addBlocks 1
        >> handleAll

        )
    ]
    where
        handleAll = traverse_ handleBlockchainEvents [user, mirror, credentialManager, issuer]
