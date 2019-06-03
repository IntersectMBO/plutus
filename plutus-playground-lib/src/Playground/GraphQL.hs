{-# LANGUAGE DataKinds            #-}
{-# LANGUAGE DeriveGeneric        #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE NamedFieldPuns       #-}
{-# LANGUAGE OverloadedStrings    #-}
{-# LANGUAGE RecordWildCards      #-}
{-# LANGUAGE ScopedTypeVariables  #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE TypeSynonymInstances #-}

module Playground.GraphQL
    ( run
    , API
    ) where

import           Control.Monad.IO.Class (liftIO)
import           Data.Monoid            ((<>))
import           Data.Morpheus          (interpreter)
import           Data.Morpheus.Types    ((::->), GQLArgs, GQLQuery, GQLRequest, GQLResponse, GQLRoot (GQLRoot),
                                         Resolver (Resolver), mutationResolver, queryResolver, subscriptionResolver)
import           Data.Text              (Text)
import           GHC.Generics           (Generic)
import           Servant                ((:>), Handler, JSON, Post, ReqBody)

type API = ReqBody '[ JSON] GQLRequest :> Post '[ JSON] GQLResponse

newtype Username =
    Username
        { username :: Text
        }
    deriving (Generic)

instance GQLArgs Username

newtype APIQuery =
    APIQuery
        { greeting :: Username ::-> Text
        }
    deriving (Generic)

instance GQLQuery APIQuery

handleGreeting :: Username ::-> Text
handleGreeting =
    Resolver $ \Username {username} -> pure $ Right $ "Hello " <> username

rootQuery :: GQLRoot APIQuery () ()
rootQuery = GQLRoot {..}
  where
    queryResolver = APIQuery {greeting = handleGreeting}
    mutationResolver = ()
    subscriptionResolver = ()

run :: GQLRequest -> Handler GQLResponse
run = liftIO . interpreter rootQuery
