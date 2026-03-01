module Main where

import Certifier.Common (loadFrom, testScripts)
import Control.DeepSeq (force)
import Control.Exception (evaluate)
import Control.Monad
import Criterion.Main
import FFI.SimplifierTrace
import FFI.Untyped (UTerm)
import MAlonzo.Code.Certifier (runCertifierMain)

certify :: Trace UTerm -> ()
certify trace = case runCertifierMain trace of
  Just (True, _) -> ()
  _ -> error "Certification failed"

main :: IO ()
main = do
  traces <- traverse (evaluate . force <=< loadFrom) testScripts
  defaultMain $
    fmap
      (\(name, trace) -> bench name $ nf certify trace)
      (zip testScripts traces)
