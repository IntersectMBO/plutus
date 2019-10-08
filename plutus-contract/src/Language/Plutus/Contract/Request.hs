{-# LANGUAGE AllowAmbiguousTypes  #-}
{-# LANGUAGE ConstraintKinds      #-}
{-# LANGUAGE DataKinds            #-}
{-# LANGUAGE DeriveGeneric        #-}
{-# LANGUAGE DerivingVia          #-}
{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE GADTs                #-}
{-# LANGUAGE OverloadedLabels     #-}
{-# LANGUAGE PolyKinds            #-}
{-# LANGUAGE RankNTypes           #-}
{-# LANGUAGE TypeApplications     #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}
module Language.Plutus.Contract.Request where

import           Control.Applicative
import           Control.Monad                      (MonadPlus)
import           Control.Monad.Except               (MonadError (throwError))
import qualified Data.Aeson                         as Aeson
import           Data.Row
import           Data.String                        (IsString)
import           Data.Text                          (Text)
import           GHC.Generics                       (Generic)

import           Language.Plutus.Contract.Resumable
import           Language.Plutus.Contract.Schema    (Event (..), Handlers (..), Input, Output)
import qualified Language.Plutus.Contract.Schema    as Events

import qualified Language.PlutusTx.Applicative      as PlutusTx
import qualified Language.PlutusTx.Functor          as PlutusTx
import           Prelude                            as Haskell

-- | A list of errors produced by a `Contract`
newtype ContractError = ContractError { unContractError :: Text }
  deriving stock (Eq, Ord, Show, Generic)
  deriving newtype (Aeson.FromJSON, Aeson.ToJSON, IsString)

-- | Throw a 'ContractError'
throwContractError :: (MonadError ContractError m) => Text -> m a
throwContractError = throwError . ContractError

-- | @Contract s a@ is a contract with schema 's', producing a value of
--  type 'a' or a 'ContractError'. See note [Contract Schema].
--
newtype Contract s a = Contract { unContract :: Resumable ContractError (Step (Maybe (Event s)) (Handlers s)) a }
  deriving newtype (Functor, Applicative, Monad, MonadError ContractError, Alternative, MonadPlus)

instance PlutusTx.Functor (Contract s) where
  fmap = Haskell.fmap

instance PlutusTx.Applicative (Contract s) where
  (<*>) = (Haskell.<*>)
  pure  = Haskell.pure

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
  :: forall l req resp s.
    ( KnownSymbol l
    , HasType l resp (Input s)
    , HasType l req (Output s)
    , ContractRow s
    )
    => req
    -> Contract s resp
request out = Contract $ CStep (Step go) where
  upd = Left $ Events.initialise @s @l out
  go Nothing = upd
  go (Just (Event rho)) = case trial rho (Label @l) of
    Left resp -> Right resp
    _         -> upd

-- | Write a request repeatedly until the desired response is returned.
requestMaybe
  :: forall l req resp s a.
     ( KnownSymbol l
     , HasType l resp (Input s)
     , HasType l req (Output s)
     , ContractRow s
     )
    => req
    -> (resp -> Maybe a)
    -> Contract s a
requestMaybe out check = do
  rsp <- request @l @req @resp @s out
  case check rsp of
    Nothing -> requestMaybe @l @req @resp @s out check
    Just a  -> pure a

-- | @select@ returns the contract that finished first, discarding the other
--   one.
--
select :: forall s a. Contract s a -> Contract s a -> Contract s a
select = (<|>)

checkpoint :: forall s a. (Aeson.FromJSON a, Aeson.ToJSON a) => Contract s a -> Contract s a
checkpoint = Contract . CJSONCheckpoint . unContract
