module Main where

import Certifier.Common (loadFrom, testScripts)
import Criterion.Main
import FFI.SimplifierTrace
import FFI.Untyped (UTerm)
import MAlonzo.Code.VerifiedCompilation (runCertifierMain)

certify :: Trace UTerm -> ()
certify trace = case runCertifierMain trace of
  Just True -> ()
  _ -> error "Certification failed"

main :: IO ()
main = do
  traces <- traverse loadFrom testScripts
  defaultMain $
    fmap
      (\(name, trace) -> bench name $ nf certify trace)
      (zip testScripts traces)
