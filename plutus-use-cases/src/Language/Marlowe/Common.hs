{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DefaultSignatures  #-}
{-# LANGUAGE DeriveAnyClass     #-}
{-# LANGUAGE DeriveGeneric      #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE RecordWildCards   #-}
{-# LANGUAGE RankNTypes   #-}
{-# LANGUAGE NamedFieldPuns   #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE TemplateHaskell   #-}
{-# OPTIONS -fplugin=Language.PlutusTx.Plugin
    -fplugin-opt Language.PlutusTx.Plugin:dont-typecheck #-}
{-# OPTIONS_GHC -Wno-incomplete-uni-patterns -Wno-name-shadowing #-}

module Language.Marlowe.Common where
import           Control.Applicative            ( Applicative(..) )
import           Control.Monad                  ( Monad(..)
                                                , void
                                                )
import           Control.Monad.Error.Class      ( MonadError(..) )
import           Data.Maybe                     (maybeToList)
import qualified Data.Set                       as Set

import qualified Language.PlutusTx              as PlutusTx
import           Wallet                         ( WalletAPI(..)
                                                , WalletAPIError
                                                , throwOtherError
                                                , signAndSubmit
                                                , ownPubKeyTxOut
                                                )

import           Ledger                         ( DataScript(..)
                                                , Height(..)
                                                , PubKey(..)
                                                , TxOutRef'
                                                , TxOut'
                                                , TxIn'
                                                , TxOut(..)
                                                , ValidatorScript(..)
                                                , scriptTxIn
                                                , scriptTxOut
                                                )
import qualified Ledger                         as Ledger
import Ledger.Validation
import qualified Ledger.Validation            as Validation
import qualified Language.PlutusTx.Builtins     as Builtins
import           Language.PlutusTx.Lift         ( makeLift )
import           Language.Haskell.TH          (Q, TExp)

type Timeout = Int
type Cash = Int

type Person      = PubKey

newtype IdentCC = IdentCC Int
               deriving (Eq, Ord, Show)
makeLift ''IdentCC


newtype IdentChoice = IdentChoice Int
               deriving (Eq, Ord, Show)
makeLift ''IdentChoice

newtype IdentPay = IdentPay Int
               deriving (Eq, Ord, Show)
makeLift ''IdentPay

type ConcreteChoice = Int

type CCStatus = (Person, CCRedeemStatus)

data CCRedeemStatus = NotRedeemed Cash Timeout
               deriving (Eq, Ord, Show)
makeLift ''CCRedeemStatus

type Choice = ((IdentChoice, Person), ConcreteChoice)

type Commit = (IdentCC, CCStatus)

data Value  = Committed IdentCC
            | Value Int
            | AddValue Value Value
            | MulValue Value Value
            | DivValue Value Value Value  -- divident, divisor, default value (when divisor evaluates to 0)
            | ValueFromChoice IdentChoice Person Value
            | ValueFromOracle PubKey Value -- Oracle PubKey, default value when no Oracle Value provided
                    deriving (Eq, Show)

makeLift ''Value

eqValidator :: Q (TExp (ValidatorHash -> ValidatorHash -> Bool))
eqValidator = [|| \(ValidatorHash l) (ValidatorHash r) -> Builtins.equalsByteString l r ||]


eqIdentCC :: Q (TExp (IdentCC -> IdentCC -> Bool))
eqIdentCC = [|| \(IdentCC a) (IdentCC b) -> a == b ||]


equalValue :: Q (TExp (Value -> Value -> Bool))
equalValue = [|| \l r -> let

    infixr 3 &&
    (&&) :: Bool -> Bool -> Bool
    (&&) = $$(PlutusTx.and)

    eqPk :: PubKey -> PubKey -> Bool
    eqPk = $$(Validation.eqPubKey)

    eq l r = case (l, r) of
        (Committed idl, Committed idr) -> $$(eqIdentCC) idl idr
        (Value vl, Value vr) -> vl == vr
        (AddValue v1l v2l, AddValue v1r v2r) -> eq v1l v1r && eq v2l v2r
        (MulValue v1l v2l, MulValue v1r v2r) -> eq v1l v1r && eq v2l v2r
        (DivValue v1l v2l v3l, DivValue v1r v2r v3r) ->
            eq v1l v1r
            && eq v2l v2r
            && eq v3l v3r
        (ValueFromChoice (IdentChoice idl) pkl vl, ValueFromChoice (IdentChoice idr) pkr vr) ->
            idl == idr
            && pkl `eqPk` pkr
            && eq vl vr
        (ValueFromOracle pkl vl, ValueFromOracle pkr vr) -> pkl `eqPk` pkr && eq vl vr
        _ -> False
    in eq l r
    ||]