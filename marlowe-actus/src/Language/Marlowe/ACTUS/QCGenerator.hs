{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# OPTIONS_GHC -fno-warn-incomplete-uni-patterns -fno-warn-name-shadowing -fno-warn-unused-do-bind #-}
module Language.Marlowe.ACTUS.QCGenerator where

import           Language.Marlowe.ACTUS.Definitions.ContractTerms
import           Test.QuickCheck
import           Data.Time
import           Data.Time.Calendar(toGregorian)
import           Data.Time.Clock(utctDay,UTCTime)
import           Data.Time.Clock.POSIX(posixSecondsToUTCTime)

epochToDay :: Integer -> Day
epochToDay = utctDay . posixSecondsToUTCTime . fromIntegral

amount :: Gen Double
amount = choose (-100.0, 100.0)

percentage :: Gen Double
percentage = choose (-100.0, 100.0)

date :: Gen Day
date = epochToDay <$> choose (0, 1000)

contractTermsGen :: ContractTerms
contractTermsGen = ContractTerms {}


