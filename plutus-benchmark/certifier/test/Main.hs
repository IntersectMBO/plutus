module Main (main) where

import Certifier.Common (loadFrom, testScripts)
import FFI.SimplifierTrace
import FFI.Untyped (UTerm)
import MAlonzo.Code.VerifiedCompilation (runCertifierMain)
import Test.Tasty (defaultMain, testGroup)
import Test.Tasty.HUnit

certify :: Trace UTerm -> IO ()
certify trace = runCertifierMain trace @?= Just True

main :: IO ()
main = do
  traces <- traverse loadFrom testScripts
  defaultMain . testGroup "certifier" $
    fmap
      (\(name, trace) -> testCase name (certify trace))
      (zip testScripts traces)
