{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# OPTIONS_GHC -fno-warn-incomplete-uni-patterns -fno-warn-name-shadowing -fno-warn-unused-do-bind #-}
module Language.Marlowe.ACTUS.QCGenerator where

import           Language.Marlowe.ACTUS.Definitions.ContractTerms
import           Test.QuickCheck
import           Data.Time

amount :: Gen Double
amount = choose (-100.0, 100.0)

percentage :: Gen Double
percentage = choose (-100.0, 100.0)

date :: Gen Day
date = undefined -- choose (fromGregorian 2020 10 20, fromGregorian 2030 10 20)

contractTermsGen :: ContractTerms
contractTermsGen = ContractTerms {}


