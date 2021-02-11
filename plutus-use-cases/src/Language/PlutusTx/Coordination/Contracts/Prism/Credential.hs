{-# LANGUAGE DataKinds          #-}
{-# LANGUAGE DeriveAnyClass     #-}
{-# LANGUAGE DeriveGeneric      #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE NamedFieldPuns     #-}
{-# LANGUAGE NoImplicitPrelude  #-}
{-# LANGUAGE TemplateHaskell    #-}

-- | Forging policy script for credential tokens.
module Language.PlutusTx.Coordination.Contracts.Prism.Credential(
    CredentialAuthority(..)
    , Credential(..)
    , policy
    , token
    , tokens
    , tokenAccount
    ) where

import           Data.Aeson                                            (FromJSON, ToJSON)
import           Data.Hashable                                         (Hashable)
import           GHC.Generics                                          (Generic)
import qualified Language.PlutusTx                                     as PlutusTx
import           Language.PlutusTx.Coordination.Contracts.TokenAccount (Account (..))
import           Language.PlutusTx.Prelude
import           Ledger.Contexts                                       (PolicyCtx (..), txSignedBy)
import           Ledger.Crypto                                         (PubKeyHash)
import           Ledger.Scripts                                        (MonetaryPolicy, mkMonetaryPolicyScript,
                                                                        monetaryPolicyHash)
import qualified Ledger.Typed.Scripts                                  as Scripts
import           Ledger.Value                                          (TokenName, Value)
import qualified Ledger.Value                                          as Value
import qualified Prelude                                               as Haskell
import           Schema                                                (ToSchema)

-- | Entity that is authorised to forge credential tokens
newtype CredentialAuthority =
    CredentialAuthority
        { unCredentialAuthority :: PubKeyHash
        }
    deriving stock (Generic, Haskell.Eq, Haskell.Show, Haskell.Ord)
    deriving anyclass (ToJSON, FromJSON, Hashable, ToSchema)

-- | Named credential issued by a credential authority
data Credential =
    Credential
        { credAuthority :: CredentialAuthority
        , credName      :: TokenName
        }
    deriving stock (Generic, Haskell.Eq, Haskell.Show, Haskell.Ord)
    deriving anyclass (ToJSON, FromJSON, Hashable, ToSchema)

-- | The forging policy script validating the creation of credential tokens
{-# INLINABLE validateForge #-}
validateForge :: CredentialAuthority -> PolicyCtx -> Bool
validateForge CredentialAuthority{unCredentialAuthority} PolicyCtx{policyCtxTxInfo=txinfo} =
    -- the credential authority is allwoed to forge or destroy any number of
    -- tokens, so we just need to check the signature
    txinfo `txSignedBy` unCredentialAuthority

policy :: CredentialAuthority -> MonetaryPolicy
policy credential = mkMonetaryPolicyScript $
    $$(PlutusTx.compile [|| \c -> Scripts.wrapMonetaryPolicy (validateForge c) ||])
        `PlutusTx.applyCode`
            PlutusTx.liftCode credential

-- | A single credential of the given name
token :: Credential -> Value
token credential = tokens credential 1

-- | A number of credentials of the given name
tokens :: Credential -> Integer -> Value
tokens Credential{credAuthority, credName} n =
    let sym = Value.mpsSymbol (monetaryPolicyHash $ policy credAuthority)
    in Value.singleton sym credName n

-- | The 'Account' that can be spent by presenting the credential
tokenAccount :: Credential -> Account
tokenAccount Credential{credAuthority, credName} =
    let sym = Value.mpsSymbol (monetaryPolicyHash $ policy credAuthority)
    in Account (sym, credName)

PlutusTx.makeLift ''CredentialAuthority
PlutusTx.unstableMakeIsData ''CredentialAuthority
PlutusTx.makeLift ''Credential
PlutusTx.unstableMakeIsData ''Credential
