{-# LANGUAGE AllowAmbiguousTypes  #-}
{-# LANGUAGE ConstraintKinds      #-}
{-# LANGUAGE DataKinds            #-}
{-# LANGUAGE DerivingVia          #-}
{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE GADTs                #-}
{-# LANGUAGE OverloadedLabels     #-}
{-# LANGUAGE PolyKinds            #-}
{-# LANGUAGE RankNTypes           #-}
{-# LANGUAGE TemplateHaskell      #-}
{-# LANGUAGE TypeApplications     #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}
module Language.Plutus.Contract.Request where

import           Control.Applicative
import           Control.Lens
import           Control.Monad                      (MonadPlus)
import           Control.Monad.Except               (MonadError)
import qualified Data.Aeson                         as Aeson
import           Data.Row
import qualified Data.Text                          as T

import           Language.Plutus.Contract.Resumable
import           Language.Plutus.Contract.Schema    (Event (..), Handlers (..), Input, Output)
import qualified Language.Plutus.Contract.Schema    as Events
import           Ledger.Constraints.OffChain        (MkTxError)

import qualified Language.PlutusTx.Applicative      as PlutusTx
import qualified Language.PlutusTx.Functor          as PlutusTx
import           Prelude                            as Haskell
import           Wallet.API                         (WalletAPIError)
import           Wallet.Emulator.Types              (AsAssertionError (..), AssertionError)

-- | @Contract s a@ is a contract with schema 's', producing a value of
--  type 'a' or a 'ContractError'. See note [Contract Schema].
--
newtype Contract s e a = Contract { unContract :: Resumable e (Step (Maybe (Event s)) (Handlers s)) a }
  deriving newtype (Functor, Applicative, Monad, MonadError e, Alternative, MonadPlus)

instance PlutusTx.Functor (Contract s e) where
  fmap = Haskell.fmap

instance PlutusTx.Applicative (Contract s e) where
  (<*>) = (Haskell.<*>)
  pure  = Haskell.pure

data ContractError =
    WalletError WalletAPIError
    | EmulatorAssertionError AssertionError
    | OtherError T.Text
    | ConstraintResolutionError MkTxError
    deriving (Show, Eq)
makeClassyPrisms ''ContractError

-- | This lets people use 'T.Text' as their error type.
instance AsContractError T.Text where
    _ContractError = prism' (T.pack . show) (const Nothing)

instance AsAssertionError ContractError where
    _AssertionError = _EmulatorAssertionError

-- | Constraints on the contract schema, ensuring that the requests produced
--   by the contracts are 'Monoid's (so that we can produce a record with
--   requests from different branches) and that the labels of the schema are
--   unique.
type ContractRow s =
  ( Forall (Output s) Monoid
  , Forall (Output s) Semigroup
  , AllUniqueLabels (Input s)
  , AllUniqueLabels (Output s)
  )

-- | Given a schema @s@ with an entry @l .== (resp, req)@, @request r@
--   is a contract that writes the request @r@ and waits for a response of type
--   @resp@.
request
  :: forall l req resp s e.
    ( KnownSymbol l
    , HasType l resp (Input s)
    , HasType l req (Output s)
    , ContractRow s
    )
    => req
    -> Contract s e resp
request out = Contract $ CStep (Step go) where
  upd = Left $ Events.initialise @s @l out
  go Nothing = upd
  go (Just (Event rho)) = case trial rho (Label @l) of
    Left resp -> Right resp
    _         -> upd

-- | Write a request repeatedly until the desired response is returned.
requestMaybe
  :: forall l req resp s e a.
     ( KnownSymbol l
     , HasType l resp (Input s)
     , HasType l req (Output s)
     , ContractRow s
     )
    => req
    -> (resp -> Maybe a)
    -> Contract s e a
requestMaybe out check = do
  rsp <- request @l @req @resp @s out
  case check rsp of
    Nothing -> requestMaybe @l @req @resp @s out check
    Just a  -> pure a

-- | @select@ returns the contract that finished first, discarding the other
--   one.
--
select :: forall s e a. Contract s e a -> Contract s e a -> Contract s e a
select = (<|>)

checkpoint :: forall s e a. (Aeson.FromJSON a, Aeson.ToJSON a) => Contract s e a -> Contract s e a
checkpoint = Contract . CJSONCheckpoint . unContract

-- | Transform any exceptions thrown by the 'Contract' using the given function.
withContractError :: forall s e e' a. (e -> e') -> Contract s e a -> Contract s e' a
withContractError f = Contract . withResumableError f . unContract
