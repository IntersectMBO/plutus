{-# LANGUAGE OverloadedStrings #-}

module Plutus.PAB.Monitoring.Config (
      defaultConfig
    , loadConfig
    ) where

import           Cardano.BM.Configuration       (setup)
import qualified Cardano.BM.Configuration.Model as CM
import           Cardano.BM.Data.BackendKind
import           Cardano.BM.Data.Configuration  (Endpoint (..))
import           Cardano.BM.Data.Output
import           Cardano.BM.Data.Severity

-- | A default 'CM.Configuration' that logs on 'Info' and above
--   to stdout
defaultConfig :: IO CM.Configuration
defaultConfig = do
  c <- CM.empty
  CM.setMinSeverity c Info
  CM.setSetupBackends c [ KatipBK
                        , AggregationBK
                        , MonitoringBK
                        , EKGViewBK
                        ]
  CM.setDefaultBackends c [KatipBK, AggregationBK, EKGViewBK]
  CM.setSetupScribes c [ ScribeDefinition {
                          scName = "stdout"
                        , scKind = StdoutSK
                        , scFormat = ScText
                        , scPrivacy = ScPublic
                        , scRotation = Nothing
                        , scMinSev = minBound
                        , scMaxSev = maxBound
                        }]
  CM.setDefaultScribes c ["StdoutSK::stdout"]
  CM.setEKGBindAddr c $ Just (Endpoint ("localhost", 12790))
  pure c

-- | Load a 'CM.Configuration' from a YAML file.
loadConfig :: FilePath -> IO CM.Configuration
loadConfig = setup
