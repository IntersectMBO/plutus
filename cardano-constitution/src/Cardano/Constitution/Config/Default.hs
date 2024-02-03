{-# LANGUAGE TemplateHaskell #-}
module Cardano.Constitution.Config.Default
    ( defaultConstitutionConfig
    , ConstitutionConfig (..)
    ) where

import Cardano.Constitution.Config.Types
import Cardano.Constitution.DataFilePaths as DFP

import Data.Aeson.THReader as Aeson

-- | The default params rails read from "defaultConstitutionConfig.json"
--
-- NOTE: this pragma should in principle be *NOINLINE*. Because of Tx we have
-- to use *INLINABLE* instead, but I don't think it can lead to problems
-- (besides efficiency problems, too many file reads?)
{-# INLINABLE defaultConstitutionConfig #-}
defaultConstitutionConfig :: ConstitutionConfig
defaultConstitutionConfig =
    $$(Aeson.readJSONFromFile DFP.defaultConstitutionConfigFile)
