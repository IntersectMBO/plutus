{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE OverloadedStrings #-}

module PlutusCore.Crypto.Utils
  ( failWithMessage
  , byteStringAsHex
  , cryptoDisabled
  ) where

import PlutusCore.Builtin.Result
  ( BuiltinResult
  , builtinResultFailure
  , emit
  )

import Data.ByteString (ByteString, foldr')
import Data.Kind (Type)
import Data.Text (Text)
import Text.Printf (printf)

{- Note [The with-crypto flag]
The cryptographic builtins (the hashes, the signature-verification primitives,
and the BLS12-381 primitives) are implemented in cardano-crypto-class, which
binds the C libraries libsodium, libblst and libsecp256k1. Because Cabal resolves
a package's @pkgconfig-depends@ at solve time for the whole package (see
https://github.com/haskell/cabal/issues/4087), merely depending on
cardano-crypto-class forces those C libraries to be present in order to even
/configure/ a build — which makes it impossible to write and compile a Plinth/
Plutus script in an environment that does not have them installed.

The @with-crypto@ Cabal flag (enabled by default) controls this. When it is on,
the modules under @PlutusCore.Crypto@ link cardano-crypto-class and behave
exactly as before. When it is off (@-with-crypto@), those modules compile a
C-free stub instead: the builtin /types/ (e.g. BLS12-381 group elements) keep a
representation good enough for the universe and the compiler, but the builtin
/operations/ are replaced by 'cryptoDisabled'. The upshot is that a @-with-crypto@
build links no C cryptography library and can therefore be configured and built
anywhere, and Plinth scripts that use the cryptographic builtins can still be
COMPILED — but those builtins cannot be EVALUATED in such a build.

The default build (@with-crypto@) is completely unchanged, so on-chain
evaluation, conformance and costing are unaffected. -}

-- | The denotation of a cryptographic builtin in a @-with-crypto@ build: the
-- operation is unavailable because the C cryptography libraries were not linked.
-- Used only by the C-free stubs under "PlutusCore.Crypto"; see
-- Note [The with-crypto flag].
cryptoDisabled :: forall (a :: Type). String -> a
cryptoDisabled op =
  error $
    "This build of Plutus Core was compiled without cryptographic support \
    \(the with-crypto Cabal flag is disabled), so the builtin "
      <> op
      <> " cannot be evaluated. Rebuild with the with-crypto flag enabled to \
         \obtain an evaluator that links the C cryptography libraries."

failWithMessage :: forall (a :: Type). Text -> Text -> BuiltinResult a
failWithMessage location reason = do
  emit $ location <> ": " <> reason
  builtinResultFailure

byteStringAsHex :: ByteString -> String
byteStringAsHex bs = "0x" ++ (Prelude.concat $ foldr' (\w s -> (printf "%02x" w) : s) [] bs)
