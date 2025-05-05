module Certifier (runCertifier) where

import FFI.AgdaUnparse (agdaUnparse)
import FFI.SimplifierTrace (mkFfiSimplifierTrace)
import FFI.Untyped (UTerm)

import UntypedPlutusCore qualified as UPLC
import UntypedPlutusCore.Transform.Simplifier

import MAlonzo.Code.VerifiedCompilation (runCertifierMain)

-- | Run the Agda certifier on the simplification trace, if requested
runCertifier
  :: Maybe String
  -- ^ Should we run the Agda certifier? If so, what should the certificate file be called?
  -> SimplifierTrace UPLC.Name UPLC.DefaultUni UPLC.DefaultFun a
  -- ^ The trace produced by the simplification process
  -> IO ()
runCertifier (Just certName) simplTrace = do
  let rawAgdaTrace = mkFfiSimplifierTrace simplTrace
  case runCertifierMain rawAgdaTrace of
    Just True ->
      putStrLn "The compilation was successfully certified."
    Just False ->
      putStrLn
        "The compilation was not successfully certified. \
        \Please open a bug report at https://www.github.com/IntersectMBO/plutus \
        \and attach the faulty certificate."
    Nothing ->
      putStrLn
        "The certifier was unable to check the compilation. \
        \Please open a bug report at https://www.github.com/IntersectMBO/plutus."
  writeFile (certName ++ ".agda") (rawCertificate certName rawAgdaTrace)
runCertifier Nothing _ = pure ()

rawCertificate :: String -> [(SimplifierStage, (UTerm, UTerm))] -> String
rawCertificate certName rawTrace =
  "module " <> certName <> " where\
  \\n\
  \\nopen import VerifiedCompilation\
  \\nopen import VerifiedCompilation.Certificate\
  \\nopen import Untyped\
  \\nopen import RawU\
  \\nopen import Builtin\
  \\nopen import Data.Unit\
  \\nopen import Data.Nat\
  \\nopen import Data.Integer\
  \\nopen import Utils\
  \\nimport Agda.Builtin.Bool\
  \\nimport Relation.Nullary\
  \\nimport VerifiedCompilation.UntypedTranslation\
  \\nopen import Agda.Builtin.Maybe\
  \\nopen import Data.Empty using (⊥)\
  \\nopen import Data.Bool.Base using (Bool; false; true)\
  \\nopen import Agda.Builtin.Equality using (_≡_; refl)\
  \\n\
  \\nasts : List (SimplifierTag × Untyped × Untyped)\
  \\nasts = " <> agdaUnparse rawTrace <>
  "\n\
  \\ncertificate : passed? (runCertifier asts) ≡ true\
  \\ncertificate = refl\
  \\n"
