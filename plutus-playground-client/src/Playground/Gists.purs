module Playground.Gists
  ( mkNewGist
  , gistSourceFilename
  , gistSimulationFilename
  , playgroundGistFile
  , simulationGistFile
  ) where

import Cursor (Cursor)
import Data.Array (catMaybes)
import Data.Array as Array
import Data.Maybe (Maybe(..))
import Data.Newtype (unwrap)
import Foreign.Generic (encodeJSON)
import Gist (Gist, GistFile, NewGist(NewGist), NewGistFile(NewGistFile))
import Gists (firstMatch)
import Language.Haskell.Interpreter (SourceCode)
import Playground.Types (Simulation)
import Prelude (($), (<$>), (<<<))

mkNewGist ::
  { source :: Maybe SourceCode
  , simulations :: Cursor Simulation
  } ->
  Maybe NewGist
mkNewGist { source, simulations } =
  if Array.null gistFiles then
    Nothing
  else
    Just
      $ NewGist
          { _newGistDescription: "Plutus Playground Smart Contract"
          , _newGistPublic: true
          , _newGistFiles: gistFiles
          }
  where
  gistFiles =
    catMaybes
      [ mkNewGistFile gistSourceFilename <<< unwrap <$> source
      , Just (mkNewGistFile gistSimulationFilename $ encodeJSON simulations)
      ]

  mkNewGistFile _newGistFilename _newGistFileContent =
    NewGistFile
      { _newGistFilename
      , _newGistFileContent
      }

gistSourceFilename :: String
gistSourceFilename = "Playground.hs"

gistSimulationFilename :: String
gistSimulationFilename = "Simulation.json"

playgroundGistFile :: Gist -> Maybe GistFile
playgroundGistFile = firstMatch gistSourceFilename

simulationGistFile :: Gist -> Maybe GistFile
simulationGistFile = firstMatch gistSimulationFilename
