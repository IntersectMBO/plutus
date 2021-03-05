{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds     #-}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE MonoLocalBinds      #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeOperators       #-}
-- | Send notifications to other contract instances
module Language.Plutus.Contract.Effects.Notify where

import           Data.Aeson                                      (ToJSON (toJSON), Value)
import           Data.Foldable                                   (traverse_)
import           Data.Proxy                                      (Proxy (..))
import           Data.Row
import           Language.Plutus.Contract.Effects.ExposeEndpoint (HasEndpoint, endpointDescription)
import           Language.Plutus.Contract.Request                (ContractRow)
import qualified Language.Plutus.Contract.Request                as R
import           Language.Plutus.Contract.Schema                 (Event (..), Handlers (..), Input, Output)
import           Language.Plutus.Contract.Types                  (Contract, mapError, throwError)
import           Wallet.Types                                    (ContractInstanceId, Notification (..),
                                                                  NotificationError (..))

type NotifySym = "notify-instance"

type HasContractNotify s =
    ( HasType NotifySym Notification (Output s)
    , HasType NotifySym (Maybe NotificationError) (Input s)
    , ContractRow s
    )

type ContractInstanceNotify = NotifySym .== (Maybe NotificationError, Notification)

-- | Send a notification to an instance of another contract whose schema
--   is known. (This provides slightly more type-safety than 'notifyInstanceUnsafe')
--
--   TODO: In the future the runtime should check that the contract instance
--   does indeed conform with 'otherSchema'.
notifyInstance :: forall ep a otherSchema w s.
    ( HasContractNotify s
    , HasEndpoint ep a otherSchema
    , ToJSON a
    )
    => ContractInstanceId
    -> a
    -> Contract w s NotificationError ()
notifyInstance i v = notifyInstanceUnsafe @ep i (toJSON v)

-- | Send a notification to a contract instance.
notifyInstanceUnsafe :: forall ep w s.
    ( HasContractNotify s
    , KnownSymbol ep
    )
    => ContractInstanceId
    -> Value
    -> Contract w s NotificationError ()
notifyInstanceUnsafe i a = do
    let notification = Notification
            { notificationContractID = i
            , notificationContractEndpoint = endpointDescription (Proxy @ep)
            , notificationContractArg = a
            }
    r <- mapError OtherNotificationError
            $ R.request @w @NotifySym @_ @_ @s notification
    traverse_ throwError r


event
    :: forall s.
    ( HasContractNotify s )
    => Maybe NotificationError
    -> Event s
event = Event . IsJust (Label @NotifySym)

request
    :: forall s.
    ( HasContractNotify s )
    => Handlers s
    -> Maybe Notification
request (Handlers r) = trial' r (Label @NotifySym)
