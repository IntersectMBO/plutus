{-# LANGUAGE TemplateHaskell #-}
module Cardano.Constitution.Config.Static.Default
    ( defaultConstitutionConfigStatic
    , ConstitutionConfigStatic(..)
    ) where

import Cardano.Constitution.Config.Default
import Cardano.Constitution.Config.Static.TH

{-# INLINABLE defaultConstitutionConfigStatic #-}
defaultConstitutionConfigStatic :: ConstitutionConfigStatic
defaultConstitutionConfigStatic = $(toConfigStatic defaultConstitutionConfig)
