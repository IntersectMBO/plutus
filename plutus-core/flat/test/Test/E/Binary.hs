{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE StandaloneDeriving #-}

module Test.E.Binary where

import Data.Binary
import Test.E

deriving instance Binary E2
deriving instance Binary E4
deriving instance Binary E8
deriving instance Binary E16
deriving instance Binary E32
deriving instance Binary E256
deriving instance Binary E258

-- fs =
--     [ Binary E2_1
--     , Binary E32_1
--     , Binary E256_255
--     , Binary E256_254
--     , Binary E256_253
--     , Binary E256_256
--     ]
