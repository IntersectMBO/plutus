{-# LANGUAGE DeriveAnyClass    #-}
{-# LANGUAGE DeriveGeneric     #-}
{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards   #-}
{-# LANGUAGE TemplateHaskell   #-}
{-# OPTIONS_GHC -Wno-unused-imports #-}
module Messages where
-- TRIM TO HERE
-- Contract endpoints that generate different kinds of errors for the log:
-- logAMessage produces a log message from a wallet
-- submitInvalidTxn submits an invalid txn which should result in a "Validation failed" message
-- throwWalletAPIError throws an error from a wallet (client)
import           Language.PlutusTx.Prelude
import           Playground.Contract

import qualified Data.Map                  as Map
import           Data.Morpheus.Types       (GQLArgs, GQLRootResolver (GQLRootResolver, mutationResolver, queryResolver, subscriptionResolver),
                                            MUTATION, ResolveCon, Resolver)
import qualified Data.Set                  as Set
import           Data.Text                 (Text)
import qualified Data.Text                 as Text
import           Ledger                    (Tx (Tx), Value, txFee, txForge, txInputs, txOutputs, txSignatures,
                                            txValidRange)
import qualified Ledger.Ada                as Ada
import           Ledger.Validation         ()
import           Wallet                    (MonadWallet, defaultSlotRange, logMsg, submitTxn, throwOtherError)

logAMessage :: MonadWallet m => m ()
logAMessage = logMsg "wallet log"

submitInvalidTxn :: MonadWallet m => m ()
submitInvalidTxn = do
    logMsg "Preparing to submit an invalid transaction"
    let tx = Tx
            { txInputs = Set.empty
            , txOutputs = []
            , txForge = Ada.adaValueOf 2
            , txFee = 0
            , txValidRange = defaultSlotRange
            , txSignatures = Map.empty
            }
    submitTxn tx

throwWalletAPIError :: MonadWallet m => Text -> m ()
throwWalletAPIError = throwOtherError

------------------------------------------------------------
-- TODO Template Haskellise.
------------------------------------------------------------
data ThrowWalletAPIErrorArguments = ThrowWalletAPIErrorArguments
  { throwWalletAPIErrorMsg :: Text
  } deriving (Generic, GQLArgs)

data MutationAPI m =
    MutationAPI
        { mutationAPILogAMessage         :: Resolver m MUTATION ()                           Bool
        , mutationAPISubmitInvalidTxn    :: Resolver m MUTATION ()                           Bool
        , mutationAPIThrowWalletAPIError :: Resolver m MUTATION ThrowWalletAPIErrorArguments Bool
        , mutationAPIPayToWallet         :: Resolver m MUTATION PayToWalletArguments         Bool
        }
    deriving (Generic)

rootResolver :: (ResolveCon m () (MutationAPI m) (), MonadWallet m) => GQLRootResolver m () (MutationAPI m) ()
rootResolver =
    GQLRootResolver
        { queryResolver = ()
        , mutationResolver =
              MutationAPI
                  { mutationAPILogAMessage = liftUnitResolver (const logAMessage)
                  , mutationAPISubmitInvalidTxn = liftUnitResolver (const submitInvalidTxn)
                  , mutationAPIThrowWalletAPIError = liftUnitResolver (\ThrowWalletAPIErrorArguments {..} -> throwWalletAPIError throwWalletAPIErrorMsg)
                  , mutationAPIPayToWallet = payToWalletResolver
                  }
        , subscriptionResolver = ()
        }

schema :: SchemaText
schema = toSchema rootResolver
