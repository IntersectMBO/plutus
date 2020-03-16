{-# LANGUAGE DataKinds          #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleContexts   #-}
{-# LANGUAGE GADTs              #-}
{-# LANGUAGE LambdaCase         #-}
{-# LANGUAGE TemplateHaskell    #-}
{-# LANGUAGE TypeOperators      #-}
module Wallet.Emulator.Diagnostics where

import           Control.Monad.Freer
import           Control.Monad.Freer.State
import           Control.Monad.Freer.TH
import           Data.Sequence             (Seq)
import qualified Data.Sequence             as Seq
import           Data.Text                 (Text)

data WalletDiagnosticsEffect r where
  WriteLogMessage :: Text -> WalletDiagnosticsEffect ()
makeEffect ''WalletDiagnosticsEffect

newtype DiagnosticsState =
    DiagnosticsState
        { _dsMessages :: Seq Text
        }
        deriving stock (Eq, Ord, Show)
        deriving newtype (Semigroup, Monoid)

handleWalletDiagnostics
    :: (Member (State DiagnosticsState) effs)
    => Eff (WalletDiagnosticsEffect ': effs) ~> Eff effs
handleWalletDiagnostics = interpret $ \case
    WriteLogMessage msg -> modify (<> (DiagnosticsState (Seq.singleton msg)))
