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

import           Control.Monad.IO.Class       (MonadIO, liftIO)
import           Data.Either                  (either)
import           Data.Morpheus                (interpreter)
import           Data.Morpheus.Kind           (KIND, OBJECT, UNION)
import           Data.Morpheus.Types          (GQLArgs, GQLRequest, GQLResponse, GQLRootResolver (GQLRootResolver, mutationResolver, queryResolver, subscriptionResolver),
                                               GQLType, MUTATION, QUERY, Resolver (Resolver), WithEffect, withEffect)
import           Data.Text                    (Text)
import qualified Data.Text                    as Text
import           GHC.Generics                 (Generic)
import           Language.Haskell.Interpreter (CompilationError (CompilationError, RawError), InterpreterResult,
                                               SourceCode, column, filename, row, text)
import           Language.Haskell.Interpreter (SourceCode)
import qualified Language.Haskell.Interpreter as HI
import           Playground.API               (CompilationResult (CompilationResult), Evaluation,
                                               EvaluationResult (EvaluationResult), SchemaText (SchemaText),
                                               adaCurrency, functionSchema, knownCurrencies)
import           Playground.Server            (acceptSourceCode2, runFunction2)
import           Servant                      ((:>), Handler, JSON, Post, ReqBody)

type API = ReqBody '[ JSON] GQLRequest :> Post '[ JSON] GQLResponse

data ContractArgs =
    ContractArgs
        { contractArgsSourceCode :: SourceCode
        }
    deriving (Generic, GQLType, GQLArgs)

data ContractResponse
    = InterpreterFailure HI.InterpreterError
    | InterpreterSuccess (InterpreterResult CompilationResult)
    deriving (Generic, GQLType)

type instance KIND ContractResponse = UNION

data APIQuery m =
    APIQuery
        { contract :: Resolver m QUERY ContractArgs ContractResponse
        , evaluate :: Resolver m QUERY Evaluation EvaluationResult
        }
    deriving (Generic)

compileContract :: MonadIO m => Resolver m QUERY ContractArgs ContractResponse
compileContract =
    Resolver $ \ContractArgs {..} ->
        Right . either InterpreterFailure InterpreterSuccess <$>
        acceptSourceCode2 contractArgsSourceCode

evaluateScenario :: MonadIO m => Resolver m QUERY Evaluation EvaluationResult
evaluateScenario = Resolver $ \args -> Right <$> runFunction2 args

rootResolver :: MonadIO m => GQLRootResolver m (APIQuery m) () ()
rootResolver = GQLRootResolver {..}
  where
    queryResolver =
        APIQuery {contract = compileContract, evaluate = evaluateScenario}
    mutationResolver = ()
    subscriptionResolver = ()

run :: GQLRequest -> Handler GQLResponse
run = liftIO . interpreter rootResolver
