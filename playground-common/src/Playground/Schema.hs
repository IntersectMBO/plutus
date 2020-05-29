{-# LANGUAGE AllowAmbiguousTypes   #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NamedFieldPuns        #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeOperators         #-}
{-# OPTIONS_GHC -fno-warn-unticked-promoted-constructors #-}

{-| This module handles exposing a Contract API to the Plutus Playground frontend.

In practice this means having a way of turning the Contract's effect
rows into a Schema declaration, by using an 'EndpointToSchema'
instance.

Typically you'll call this as 'endpointsToSchemas (mySchema .\\ BlockchainActions)'
to filter the special endpoints that don't need a Schema.
|-}
module Playground.Schema
    ( endpointsToSchemas
    , EndpointToSchema
    ) where

import           Data.Kind                                       (Type)
import           Data.Row                                        (Empty, KnownSymbol, Label (Label))
import           Data.Row.Internal                               (LT ((:->)), Row (R))
import           Language.Plutus.Contract.Effects.ExposeEndpoint (ActiveEndpoints,
                                                                  EndpointDescription (EndpointDescription),
                                                                  EndpointValue)
import           Language.Plutus.Contract.Schema                 ()
import           Playground.Types                                (FunctionSchema (FunctionSchema), arguments,
                                                                  endpointDescription)
import           Schema                                          (FormSchema, ToSchema, toSchema)

class EndpointToSchema (s :: Row Type) where
    endpointsToSchemas :: [FunctionSchema FormSchema]

instance EndpointToSchema Empty where
    endpointsToSchemas = []

instance (ToSchema params, KnownSymbol label, EndpointToSchema (R bs)) =>
         EndpointToSchema (R (label :-> (EndpointValue params, ActiveEndpoints) : bs)) where
    endpointsToSchemas =
        FunctionSchema {endpointDescription, arguments} : endpointsToSchemas @(R bs)
      where
        endpointDescription = EndpointDescription . show $ Label @label
        arguments = [toSchema @params]
