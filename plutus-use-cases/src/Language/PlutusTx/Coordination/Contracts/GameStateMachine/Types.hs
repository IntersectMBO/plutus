{-# LANGUAGE DataKinds         #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell   #-}
{-# LANGUAGE TypeApplications  #-}
{-# OPTIONS_GHC -fno-ignore-interface-pragmas #-}
{-# OPTIONS_GHC -fno-omit-interface-pragmas #-}
module Language.PlutusTx.Coordination.Contracts.GameStateMachine.Types where


import qualified Language.PlutusTx              as PlutusTx
import           Language.PlutusTx.Prelude
import           Ledger.Value                   (TokenName)
import qualified Ledger.Value                   as V

import           Language.PlutusTx.StateMachine ()

newtype HashedString = HashedString ByteString

PlutusTx.makeLift ''HashedString

newtype ClearString = ClearString ByteString

PlutusTx.makeLift ''ClearString

-- | State of the guessing game
data GameState =
    Initialised HashedString
    -- ^ Initial state. In this state only the 'ForgeTokens' action is allowed.
    | Locked TokenName HashedString
    -- ^ Funds have been locked. In this state only the 'Guess' action is
    --   allowed.

instance Eq GameState where
    {-# INLINABLE (==) #-}
    (Initialised (HashedString s)) == (Initialised (HashedString s')) = s == s'
    (Locked (V.TokenName n) (HashedString s)) == (Locked (V.TokenName n') (HashedString s')) = s == s' && n == n'
    _ == _ = traceIfFalseH "states not equal" False

PlutusTx.makeLift ''GameState
