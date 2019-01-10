-- Contract endpoints that generate different kinds of errors for the log:
-- logAMessage produces a log message from a wallet
-- submitInvalidTxn submits an invalid txn which should result in a "Validation failed" message
-- throwWalletAPIError throws an error from a wallet (client)
import qualified Data.Set                     as Set
import           Data.Text                    (Text)

import           Ledger
import           Ledger.Validation
import           Wallet
import           Playground.Contract

logAMessage :: MockWallet ()
logAMessage = logMsg "wallet log"

submitInvalidTxn :: MockWallet ()
submitInvalidTxn = do
    logMsg "Preparing to submit an invalid transaction"
    let tx = Tx
            { txInputs = Set.empty
            , txOutputs = []
            , txForge = 2
            , txFee = 0
            }
    submitTxn tx

throwWalletAPIError :: Text -> MockWallet ()
throwWalletAPIError = throwOtherError

$(mkFunctions ['logAMessage, 'submitInvalidTxn, 'throwWalletAPIError])
