-- | Provides a simple main function which runs all the tests
--
module Main
    ( main
    ) where

import Test.Framework (defaultMain)

import qualified Tests.Buffer as Buffer
import qualified Tests.Properties as Properties
import qualified Tests.Regressions as Regressions
import qualified Tests.Marshal as Marshal

main :: IO ()
main = defaultMain [Buffer.tests, Properties.tests, Regressions.tests, Marshal.tests]
