{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE DeriveAnyClass      #-}
{-# LANGUAGE DeriveGeneric       #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE NamedFieldPuns      #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE RecordWildCards     #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies        #-}
{-# LANGUAGE TypeOperators       #-}

module Playground.GraphQL where

import           Control.Monad.IO.Class       (liftIO)
import           Data.Morpheus                (interpreter)
import           Data.Morpheus.Kind           (KIND, OBJECT)
import           Data.Morpheus.Types          (GQLArgs, GQLRequest, GQLResponse, GQLResponse, GQLRootResolver (GQLRootResolver, mutationResolver, queryResolver, subscriptionResolver),
                                               MUTATION, QUERY, Resolver (Resolver), withEffect)
import           Data.Text                    (Text)
import qualified Data.Text                    as Text
import           GHC.Generics                 (Generic)
import           Language.Haskell.Interpreter (SourceCode)
import           Playground.API               (CompilationResult (CompilationResult), SchemaText (SchemaText),
                                               adaCurrency, functionSchema, knownCurrencies)
import           Servant                      ((:>), Handler, JSON, Post, ReqBody)

type API = ReqBody '[ JSON] GQLRequest :> Post '[ JSON] GQLResponse

type instance KIND User = OBJECT

data User =
    User
        { userName :: Text
        , userAge  :: Int
        }
    deriving (Generic, GQLArgs)

data ContractArgs =
    ContractArgs
        { contractArgsSource :: SourceCode
        , contractArgsSize   :: Int
        }
    deriving (Generic)

instance GQLArgs ContractArgs

newtype APIQuery m =
    APIQuery
        { greeting :: Resolver m QUERY User Text
        }
    deriving (Generic)

newtype APIMutation m =
    APIMutation
        { contract :: Resolver m MUTATION ContractArgs CompilationResult
        -- , contract :: SourceCode ::-> Either HI.InterpreterError (InterpreterResult CompilationResult)
        -- , evaluate :: Evaluation ::-> EvaluationResult
        }
    deriving (Generic)

compileContract :: Monad m => Resolver m MUTATION ContractArgs CompilationResult
compileContract =
    Resolver $ \ContractArgs {..} ->
        pure $
        withEffect [] $
        Right $
        CompilationResult
            { functionSchema = SchemaText "TODO"
            , knownCurrencies = [adaCurrency]
            }

handleGreeting :: Monad m => Resolver m QUERY User Text
handleGreeting =
    Resolver $ \User {..} ->
        pure $
        Right $ "Hello " <> userName <> " (" <> Text.pack (show userAge) <> ")"

rootResolver :: Monad m => GQLRootResolver m (APIQuery m) (APIMutation m) ()
rootResolver = GQLRootResolver {..}
  where
    queryResolver =
        APIQuery
            { greeting = handleGreeting
            }
    mutationResolver =
        APIMutation
            { contract = compileContract
            -- , evaluate = evaluateScenario
            }
    subscriptionResolver = ()

run :: GQLRequest -> Handler GQLResponse
run = liftIO . interpreter rootResolver
