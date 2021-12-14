{-# LANGUAGE NoImplicitPrelude   #-}
{-# LANGUAGE OverloadedStrings   #-}
module Test.Basement
    ( tests
    ) where

import Foundation
import Foundation.Check
import qualified Test.Basement.UTF8 as UTF8

tests = Group "basement"
    [ UTF8.tests
    ]
