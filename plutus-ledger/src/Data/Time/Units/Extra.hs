{-# LANGUAGE TypeApplications #-}
{-# OPTIONS_GHC   -Wno-orphans #-}

module Data.Time.Units.Extra where

import           Data.Aeson      (FromJSON, ToJSON, parseJSON, toJSON, withScientific)
import           Data.Scientific (toBoundedInteger)
import           Data.Time.Units (Millisecond, Second)

instance FromJSON Second where
    parseJSON =
        withScientific
            "second"
            (\s ->
                 case toBoundedInteger s of
                     Nothing -> fail "Value must be an Integer."
                     Just i  -> pure (fromIntegral (i :: Int)))

instance ToJSON Second where
    toJSON = toJSON @Int . fromIntegral

instance FromJSON Millisecond where
    parseJSON =
        withScientific
            "millisecond"
            (\s ->
                 case toBoundedInteger s of
                     Nothing -> fail "Value must be an Integer."
                     Just i  -> pure (fromIntegral (i :: Int)))

instance ToJSON Millisecond where
    toJSON = toJSON @Int . fromIntegral
