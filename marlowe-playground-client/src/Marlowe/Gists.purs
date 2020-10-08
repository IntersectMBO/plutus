module Marlowe.Gists
  ( mkNewGist
  , currentSimulationMarlowe
  , oldSimulationMarlowe
  , simulationState
  , playgroundGist
  , playgroundFiles
  ) where

import Prelude
import Blockly (XML)
import Control.Monad.Except (runExcept)
import Data.Array (catMaybes)
import Data.Either (hush)
import Data.Lens (Traversal', has, view)
import Data.Lens.Index (ix)
import Data.List.NonEmpty as NEL
import Data.List.Types (NonEmptyList)
import Data.Maybe (Maybe, fromMaybe)
import Data.Newtype (unwrap, wrap)
import Foreign.Generic (decodeJSON, encodeJSON)
import Gist (Gist, NewGist(NewGist), NewGistFile(..), gistFileContent, gistFiles)
import Simulation.State (MarloweState, emptyMarloweState)

mkNewGist :: String -> PlaygroundFiles -> NewGist
mkNewGist description files =
  NewGist
    { _newGistDescription: description
    , _newGistPublic: true
    , _newGistFiles: toArray files
    }

mkNewGistFile :: String -> String -> NewGistFile
mkNewGistFile _newGistFilename _newGistFileContent =
  NewGistFile
    { _newGistFilename
    , _newGistFileContent
    }

type PlaygroundFiles
  = { playground :: String
    , currentSimulation :: Maybe String
    , oldSimulation :: Maybe String
    , simulation :: NonEmptyList MarloweState
    , marlowe :: Maybe String
    , haskell :: Maybe String
    , blockly :: Maybe XML
    , javascript :: Maybe String
    , actus :: Maybe XML
    }

toArray :: PlaygroundFiles -> Array NewGistFile
toArray { playground, currentSimulation, oldSimulation, simulation, marlowe, haskell, blockly, javascript, actus } =
  [ mkNewGistFile playgroundFilename playground
  , mkNewGistFile simulationFilename (encodeJSON stateArray)
  ]
    <> catMaybes
        [ mkNewGistFile marloweFilename <$> marlowe
        , mkNewGistFile haskellFilename <$> haskell
        , mkNewGistFile blocklyFilename <<< unwrap <$> blockly
        , mkNewGistFile jsFilename <$> javascript
        , mkNewGistFile actusFilename <<< unwrap <$> actus
        , mkNewGistFile currentSimulationMarloweFilename <$> currentSimulation
        , mkNewGistFile oldSimulationMarloweFilename <$> oldSimulation
        ]
  where
  stateArray :: Array MarloweState
  stateArray = NEL.toUnfoldable simulation

playgroundFilename :: String
playgroundFilename = "playground.marlowe.json"

currentSimulationMarloweFilename :: String
currentSimulationMarloweFilename = "CurrentMarlowe.hs"

oldSimulationMarloweFilename :: String
oldSimulationMarloweFilename = "OldMarlowe.hs"

simulationFilename :: String
simulationFilename = "simulation.json"

marloweFilename :: String
marloweFilename = "playground.marlowe"

haskellFilename :: String
haskellFilename = "Main.hs"

blocklyFilename :: String
blocklyFilename = "blockly.xml"

jsFilename :: String
jsFilename = "playground.js"

actusFilename :: String
actusFilename = "actus.xml"

currentSimulationMarlowe :: Traversal' Gist (Maybe String)
currentSimulationMarlowe = gistFiles <<< ix currentSimulationMarloweFilename <<< gistFileContent

oldSimulationMarlowe :: Traversal' Gist (Maybe String)
oldSimulationMarlowe = gistFiles <<< ix oldSimulationMarloweFilename <<< gistFileContent

simulationState :: Gist -> Maybe (NonEmptyList MarloweState)
simulationState gist = do
  content <- view (gistFiles <<< ix simulationFilename <<< gistFileContent) gist
  stateList <- hush $ runExcept $ decodeJSON content
  NEL.fromList stateList

playgroundGist :: Gist -> Boolean
playgroundGist = has (gistFiles <<< ix playgroundFilename)

playgroundFiles :: Gist -> PlaygroundFiles
playgroundFiles gist =
  { playground: fromMaybe "{}" $ getFile playgroundFilename
  , currentSimulation: getFile currentSimulationMarloweFilename
  , oldSimulation: getFile oldSimulationMarloweFilename
  , simulation: fromMaybe (pure (emptyMarloweState zero)) $ simulationState gist
  , marlowe: getFile marloweFilename
  , haskell: getFile haskellFilename
  , blockly: wrap <$> getFile blocklyFilename
  , javascript: getFile jsFilename
  , actus: wrap <$> getFile actusFilename
  }
  where
  getFile name = view (gistFiles <<< ix name <<< gistFileContent) gist
