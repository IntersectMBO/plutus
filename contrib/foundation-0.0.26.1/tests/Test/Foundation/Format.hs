{-# LANGUAGE OverloadedStrings #-}
module Test.Foundation.Format
    ( testFormat
    ) where

import Foundation
import Foundation.Check
import Test.Foundation.Format.CSV


testFormat :: Test
testFormat = Group "Format"
  [ testFormatCSV
  ]
