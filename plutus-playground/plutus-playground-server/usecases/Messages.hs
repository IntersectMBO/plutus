-- Contract endpoints that generate different kinds of errors for the log:
-- logAMessage produces a log message from a wallet
-- submitInvalidTxn submits an invalid txn which should result in a "Validation failed" message
-- throwWalletAPIError throws an error from a wallet (client)
module Language.PlutusTx.Coordination.Contracts.Messages where

import           Control.Applicative          (Applicative (..))
import           Control.Lens
import           Control.Monad                (void)
import           Control.Monad.Error          (MonadError (..))
import           Data.Foldable                (foldMap)
import qualified Data.Map                     as Map
import           Data.Maybe                   (fromMaybe)
import           Data.Monoid                  (Sum (..))
import qualified Data.Set                     as Set
import           Data.Text
import           GHC.Generics                 (Generic)
import           Playground.Contract

import qualified Language.PlutusTx            as PlutusTx
import qualified Language.PlutusTx.Validation as PlutusTx
import           Ledger
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
