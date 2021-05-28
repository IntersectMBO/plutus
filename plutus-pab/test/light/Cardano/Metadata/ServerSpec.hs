{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE ScopedTypeVariables   #-}

module Cardano.Metadata.ServerSpec
    ( tests
    ) where

import           Cardano.Metadata.Mock          (annotatedSignature1, script1)
import           Cardano.Metadata.Server        (handleMetadata)
import           Cardano.Metadata.Types         (HashFunction (SHA256), MetadataEffect, MetadataError,
                                                 MetadataLogMessage, Property (Name, Preimage),
                                                 PropertyKey (PropertyKey), Query (QuerySubjects),
                                                 QueryResult (QueryResult), SubjectProperties (SubjectProperties),
                                                 batchQuery, getProperties, getProperty, propertyNames, subjects,
                                                 toSubject)
import           Control.Monad.Freer            (Eff, runM)
import           Control.Monad.Freer.Error      (Error, runError)
import           Control.Monad.Freer.Extras.Log (LogMsg, handleLogTrace)
import           Data.List.NonEmpty             (NonEmpty ((:|)))
import qualified Data.Set                       as Set
import           Test.Tasty                     (TestName, TestTree, testGroup)
import           Test.Tasty.HUnit               (assertEqual, testCase)

tests :: TestTree
tests = testGroup "Cardano.Metadata.Server" [queryTests]

queryTests :: TestTree
queryTests =
    testGroup
        "Query Tests"
        [ assertReturns
              "GetProperties"
              (Right
                   (SubjectProperties
                        (toSubject script1)
                        [ Preimage SHA256 script1
                        , Name "Fred's Script" (annotatedSignature1 :| [])
                        ]))
              (getProperties (toSubject script1))
        , assertReturns
              "GetProperty"
              (Right (Preimage SHA256 script1))
              (getProperty (toSubject script1) (PropertyKey "preimage"))
        , assertReturns
              "Query by Subjects"
              (Right
                   (QueryResult
                        [ SubjectProperties
                              (toSubject script1)
                              [ Preimage SHA256 script1
                              , Name "Fred's Script" (annotatedSignature1 :| [])
                              ]
                        ]))
              (batchQuery
                   (QuerySubjects
                        { subjects = Set.fromList [toSubject script1]
                        , propertyNames = Nothing
                        }))
        , assertReturns
              "Query by Subjects/Properties"
              (Right
                   (QueryResult
                        [ SubjectProperties
                              (toSubject script1)
                              [Name "Fred's Script" (annotatedSignature1 :| [])]
                        ]))
              (batchQuery
                   (QuerySubjects
                        { subjects = Set.fromList [toSubject script1]
                        , propertyNames =
                              Just (Set.fromList [PropertyKey "name"])
                        }))
        ]

assertReturns ::
       (Eq a, Show a)
    => TestName
    -> Either MetadataError a
    -> Eff '[ MetadataEffect, LogMsg MetadataLogMessage, Error MetadataError, IO] a
    -> TestTree
assertReturns msg expected query =
    testCase msg $ do
        result <- runMetadata query
        assertEqual msg expected result

runMetadata ::
       Eff '[ MetadataEffect, LogMsg MetadataLogMessage, Error MetadataError, IO] a
    -> IO (Either MetadataError a)
runMetadata = runM . runError . handleLogTrace . handleMetadata
