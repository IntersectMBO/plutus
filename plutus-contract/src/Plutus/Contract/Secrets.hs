{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications  #-}
module Plutus.Contract.Secrets(
  Secret
  , SecretArgument (..)
  , mkSecret
  , secretArg
  , extractSecret
  , escape_sha2_256
  , unsafe_escape_secret
  ) where

import           Control.Monad
import           Data.Aeson                   as Aeson (FromJSON (..), ToJSON (..), Value (..))
import           Data.Aeson.Encoding.Internal (string)
import           Data.String
import           PlutusTx.Prelude             as PlutusTx
import qualified Prelude                      as Haskell

-- | A secret value. A value of type `Secret a` can't leak onto
-- the blockchain in plain-text unless you use an unsafe function.
-- However, a value of type `Secret a` can end up on the blockchain
-- via one of the escape hatches like `escape_sha2_256`.
newtype Secret a = MkSecret a

{- Note [Secret abstraction]
   A value of type `Secret a` is guaranteed not to leak (without a compiler warning)
   because of type abstraction. Intuitively, the `PlutusTx.Extensions.Secrets` module
   does not export the `MkSecret` constructor so as long as the client code that
   imports `PlutusTx.Extensions.Secrets` does not use some unholy `unsafePerformIO` to
   break the Haskell type system the code is guaranteed not to depend on the actual
   value of a secret without:
     1. Using a safe function like `escape_sha2_256` or
     2. Using an unsafe function like `unsafe_escape_secret` (which has a compiler warning
        attached to it).

   This intuition can be made formally precise (see Algehed and Bernardy 2019).

   As noted above, `unsafe_escape_secret` breaks the abstraction barrier and we need to export
   it for two reasons:
     1. To make the library backwards-compatible. If you have some new hash function you should
        be able to define `escape_my_magic_hash` without having to implement it in this module.
     2. For tests it is sometimes necessary to use `unsafe_escape_secret` to inspect the value
        of a secret.

   See `Plutus.Contracts.SealedBidAuction` or `Plutus.Contract.GameStateMachineWithSecretTypes`
   for examples.
 -}

-- | Secret argments are provided in the endpoint argument types.
--
-- This type guarantees that a `SecretArgument a` that is seen by
-- the endpoint code is a `Secret a` in a way that can not be
-- bypassed by safe code.
data SecretArgument a = UserSide a
                      | EndpointSide (Secret a)
                      deriving Haskell.Show

{- Note [Secret arguments]
   When we write endpoint code we would like to specify the argument type
   for an endpoint with code that looks something like this:
   ```
   data MyEndpointArgs = MyEndpointArgs { publicArg :: Int , secretArg :: Secret Int }

   type UserSchema = Endpoint "myendpoint" MyEndpointArgs
                     .\/ ...
   ```
   Which would mean that any endpoint code for `myendpoint` would be guaranteed not to
   leak the `secretArg` in plaintext to the blockchain (or elsewhere for that matter).

   However, the type `MyEndpointArgs` needs to be an instance of the class `ToJSON`
   for this to work out with the `endpoint` function. Consequently, we would need to
   provide a function `toJSON :: Secret a -> Value` that would have to break abstraction
   for the `Secret` type (see [Secret abstraction]) which would be bad.

   The `SecretArgument a` type fixes this by having two constructors `UserSide :: a -> SecretArgument a`
   and `EndpointSide :: Secret a -> SecretArgument a` that ensures that as secrets are submitted
   to endpoint code by the user they are "public", while when the secret reaches the endpoint code it
   has been obscured by a `Secret` wrapper that gives us the guarantee that the secret doesn't leak.

   See `Plutus.Contracts.SealedBidAuction` or `Plutus.Contract.GameStateMachineWithSecretTypes` for examples.
 -}

instance ToJSON a => ToJSON (SecretArgument a) where
  toJSON (UserSide a)     = toJSON a
  toJSON (EndpointSide _) = Aeson.String "EndpointSide *****"

  toEncoding (UserSide a)     = toEncoding a
  toEncoding (EndpointSide _) = string "EndpointSide *****"

instance FromJSON a => FromJSON (SecretArgument a) where
  parseJSON = liftM (EndpointSide Haskell.. mkSecret) Haskell.. parseJSON

instance Haskell.Show (Secret a) where
  show (MkSecret _) = "*****"

instance Haskell.Functor Secret where
  fmap f (MkSecret a) = MkSecret (f a)

instance PlutusTx.Functor Secret where
  fmap f (MkSecret a) = MkSecret (f a)

instance Haskell.Applicative Secret where
  pure = mkSecret
  (MkSecret f) <*> (MkSecret a) = MkSecret (f a)

instance PlutusTx.Applicative Secret where
  pure = MkSecret
  (MkSecret f) <*> (MkSecret a) = MkSecret (f a)

instance Monad Secret where
  MkSecret a >>= f = f a

instance IsString s => IsString (Secret s) where
  fromString = MkSecret . fromString

instance IsString s => IsString (SecretArgument s) where
  fromString = UserSide . fromString

-- | Turn a public value into a secret value
mkSecret :: a -> Secret a
mkSecret = MkSecret

-- | Construct a secret argument
secretArg :: a -> SecretArgument a
secretArg = UserSide

-- | Extract a secret value from a secret argument
extractSecret :: SecretArgument a -> Secret a
extractSecret (UserSide a)     = mkSecret a
extractSecret (EndpointSide s) = s

-- | Take the sha2_256 hash of a secret value. The result of this
-- function can be used on the blockchain.
{-# INLINABLE escape_sha2_256 #-}
escape_sha2_256 :: Secret BuiltinByteString -> BuiltinByteString
escape_sha2_256 = sha2_256 . unsafe_escape_secret

{-# WARNING unsafe_escape_secret "[Requires Review] An escape hatch is being created. This should only be used in trusted code." #-}
unsafe_escape_secret :: Secret a -> a
unsafe_escape_secret (MkSecret a) = a
