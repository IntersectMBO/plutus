module Language.PlutusTx.Coordination.Contracts.Game where

import           Control.Applicative          (Applicative (..))
import           Control.Lens
import           Control.Monad                (void)
import           Data.Foldable                (foldMap)
import qualified Data.Map                     as Map
import           Data.Maybe                   (fromMaybe)
import           Data.Monoid                  (Sum (..))
import qualified Data.Set                     as Set
import           GHC.Generics                 (Generic)
import           Playground.Contract
import           Data.Text
import           Control.Monad.Error (MonadError(..))

import qualified Language.PlutusTx            as PlutusTx
import qualified Language.PlutusTx.Validation as PlutusTx
import           Ledger as Ledger
import           Ledger.Validation
import Wallet hiding (payToPubKey)

logAMessage :: (WalletAPI m, WalletDiagnostics m) => m ()
logAMessage = logMsg "wallet log"

data ANumber = ANumber Int
    deriving (Generic, ToJSON, FromJSON, ToSchema)

PlutusTx.makeLift ''ANumber

data AGuess = AGuess Int
    deriving (Generic, ToJSON, FromJSON, ToSchema)

PlutusTx.makeLift ''AGuess

gameValidator :: ValidatorScript
gameValidator = ValidatorScript (Ledger.fromPlcCode $$(PlutusTx.plutus [||
    \(AGuess guess) (ANumber number) (p :: PendingTx ValidatorHash) ->

    if guess == number
    then ()
    else $$(PlutusTx.traceH) "WRONG!" (PlutusTx.error ())

    ||]))

gameAddress :: Address'
gameAddress = Ledger.scriptAddress gameValidator

contribute :: (WalletAPI m, WalletDiagnostics m)
    => Int
    -> Value
    -> m ()
contribute n value = do
    let ds = DataScript (Ledger.lifted (ANumber n))
    _ <- payToScript gameAddress value ds
    pure ()

guess :: (WalletAPI m, WalletDiagnostics m)
    => Int
    -> m ()
guess n = do
    let redeemer = RedeemerScript (Ledger.lifted (AGuess n))
    collectFromScript gameValidator redeemer
    -- won't worK! We need to start watching the address first!

$(mkFunction 'logAMessage)
$(mkFunction 'contribute)
$(mkFunction 'guess)
