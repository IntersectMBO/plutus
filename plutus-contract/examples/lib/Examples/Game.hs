{-# LANGUAGE ApplicativeDo              #-}
{-# LANGUAGE DataKinds                  #-}
{-# LANGUAGE DeriveAnyClass             #-}
{-# LANGUAGE DeriveGeneric              #-}
{-# LANGUAGE DerivingStrategies         #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MonoLocalBinds             #-}
{-# LANGUAGE TypeOperators              #-}
-- | Contract interface for the guessing game
module Examples.Game(
      game
    , LockParams(..)
    , GuessParams(..)
    , gameAddress
    -- * Some traces
    , lockTrace
    , guessTrace
    ) where

import           Control.Applicative                           (Alternative (..))
import           Control.Lens                                  (at, (^.))
import           Control.Monad                                 (void)
import qualified Data.Aeson                                    as Aeson
import qualified Data.Map                                      as Map
import           Data.Maybe                                    (fromMaybe)
import           GHC.Generics                                  (Generic)

import           Language.Plutus.Contract
import           Language.Plutus.Contract.Emulator
import           Language.Plutus.Contract.Tx                   (unbalancedTx)
import           Language.PlutusTx.Coordination.Contracts.Game (gameAddress, gameDataScript, gameRedeemerScript,
                                                                gameValidator)
import           Wallet.Emulator                               (MonadEmulator)
import qualified Wallet.Emulator                               as EM

import qualified Ledger                                        as L
import           Ledger.Ada                                    (Ada)
import qualified Ledger.Ada                                    as Ada
import qualified Ledger.AddressMap                             as AM

-- | Parameters for the "lock" endpoint
data LockParams = LockParams
    { secretWord :: String
    , amount     :: Ada
    }
    deriving stock (Eq, Ord, Show, Generic)
    deriving anyclass (Aeson.FromJSON, Aeson.ToJSON)

--  | Parameters for the "guess" endpoint
newtype GuessParams = GuessParams
    { guessWord :: String
    }
    deriving stock (Eq, Ord, Show, Generic)
    deriving newtype (Aeson.FromJSON, Aeson.ToJSON)

guess :: ContractActions r => Contract r ()
guess = do
    st <- nextTransactionAt gameAddress
    let mp = AM.fromTxOutputs st
    GuessParams theGuess <- endpoint "guess"
    let
        outputs  = Map.toList . fromMaybe Map.empty $ mp ^. at gameAddress
        redeemer = gameRedeemerScript theGuess
        inp      = (\o -> L.scriptTxIn (fst o) gameValidator redeemer) <$> outputs
        tx       = unbalancedTx inp []
    void (writeTx tx)

lock :: ContractActions r => Contract r ()
lock = do
    LockParams secret amt <- endpoint "lock"
    let
        vl         = Ada.toValue amt
        dataScript = gameDataScript secret
        output = L.TxOutOf gameAddress vl (L.PayToScript dataScript)
        tx     = unbalancedTx [] [output]
    void (writeTx tx)

game :: ContractActions r => Contract r ()
game = guess <|> lock

lockTrace
    :: ( MonadEmulator m )
    => ContractTrace m a ()
lockTrace =
    let w1 = EM.Wallet 1 in
    callEndpoint w1 "lock" (LockParams "secret" 10) >> handleBlockchainEvents w1

guessTrace
    :: ( MonadEmulator m )
    => ContractTrace m a ()
guessTrace =
    let w2 = EM.Wallet 2 in
    lockTrace >> callEndpoint w2 "guess" (GuessParams "secret") >> handleBlockchainEvents w2
