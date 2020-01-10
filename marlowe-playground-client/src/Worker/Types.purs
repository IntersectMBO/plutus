module Worker.Types where

import Prelude

import Data.Generic.Rep (class Generic)
import Data.Generic.Rep.Show (genericShow)

data WorkerRequest
  = AnalyseContract String
  | InitializeZ3

derive instance genericWorkerRequest :: Generic WorkerRequest _

instance showWorkerRequest :: Show WorkerRequest where
  show = genericShow

data WorkerResponse
  = AnalyseContractResult String
  | InitializedZ3

derive instance genericWorkerResponse :: Generic WorkerResponse _

instance showWorkerResponse :: Show WorkerResponse where
  show = genericShow
