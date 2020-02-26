{-# OPTIONS_GHC   -Wno-orphans #-}

module Data.Time.Units.Extra where

import           Data.Aeson      (FromJSON, parseJSON, withScientific)
import           Data.Scientific (toBoundedInteger)
import           Data.Time.Units (Second)

instance FromJSON Second where
    parseJSON =
        withScientific
            "second"
            (\s ->
                 case toBoundedInteger s of
                     Nothing -> fail "Value must be an Integer."
                     Just i  -> pure (fromIntegral (i :: Int)))
