module Worker.Types where

import Web.Event.Event (EventType(..))

data WorkerRequest
  = AnalyseContract String
  | InitializeZ3

data WorkerResponse
  = AnalyseContractResult String
  | InitializedZ3

onMessage :: EventType
onMessage = EventType "message"
