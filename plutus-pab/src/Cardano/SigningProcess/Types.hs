{-# LANGUAGE DataKinds         #-}
{-# LANGUAGE DeriveAnyClass    #-}
{-# LANGUAGE DeriveGeneric     #-}
{-# LANGUAGE DerivingVia       #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications  #-}

module Cardano.SigningProcess.Types
    ( SigningProcessMsg (..)
    ) where

import           Data.Aeson                    (FromJSON, ToJSON)
import           Data.Text.Prettyprint.Doc     (Pretty (..), (<+>))
import           GHC.Generics                  (Generic)

import           Cardano.BM.Data.Tracer        (ToObject (..))
import           Cardano.BM.Data.Tracer.Extras (Tagged (..), mkObjectStr)

newtype SigningProcessMsg =
    StartingSigningProcess Int -- ^ Starting up on the specified port
        deriving stock (Show, Generic)
        deriving anyclass (ToJSON, FromJSON)

instance Pretty SigningProcessMsg where
    pretty = \case
        StartingSigningProcess port -> "Starting Signing Process on port " <+> pretty port

instance ToObject SigningProcessMsg where
    toObject _ = \case
        StartingSigningProcess p -> mkObjectStr "starting signing process" (Tagged @"port" p)
