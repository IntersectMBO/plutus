module Marlowe.Gists
  ( mkNewGist
  , playgroundGist
  , playgroundFiles
  ) where

import Prelude
import Blockly (XML)
import Data.Array (catMaybes)
import Data.Lens (has, view)
import Data.Lens.Index (ix)
import Data.Maybe (Maybe, fromMaybe)
import Data.Newtype (unwrap, wrap)
import Gist (Gist, NewGist(NewGist), NewGistFile(..), gistFileContent, gistFiles)

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
    , marlowe :: Maybe String
    , haskell :: Maybe String
    , blockly :: Maybe XML
    , javascript :: Maybe String
    , actus :: Maybe XML
    }

toArray :: PlaygroundFiles -> Array NewGistFile
toArray { playground, marlowe, haskell, blockly, javascript, actus } =
  [ mkNewGistFile playgroundFilename playground
  ]
    <> catMaybes
        [ mkNewGistFile marloweFilename <$> marlowe
        , mkNewGistFile haskellFilename <$> haskell
        , mkNewGistFile blocklyFilename <<< unwrap <$> blockly
        , mkNewGistFile jsFilename <$> javascript
        , mkNewGistFile actusFilename <<< unwrap <$> actus
        ]

playgroundFilename :: String
playgroundFilename = "playground.marlowe.json"

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

playgroundGist :: Gist -> Boolean
playgroundGist = has (gistFiles <<< ix playgroundFilename)

playgroundFiles :: Gist -> PlaygroundFiles
playgroundFiles gist =
  { playground: fromMaybe "{}" $ getFile playgroundFilename
  , marlowe: getFile marloweFilename
  , haskell: getFile haskellFilename
  , blockly: wrap <$> getFile blocklyFilename
  , javascript: getFile jsFilename
  , actus: wrap <$> getFile actusFilename
  }
  where
  getFile name = view (gistFiles <<< ix name <<< gistFileContent) gist
