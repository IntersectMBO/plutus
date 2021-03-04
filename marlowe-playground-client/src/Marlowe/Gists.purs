module Marlowe.Gists
  ( mkNewGist
  , isPlaygroundGist
  , playgroundFiles
  , filenames
  , fileExists
  , PlaygroundFiles
  ) where

import Prelude
import Blockly.Internal (XML)
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
    , blockly :: Maybe String
    , javascript :: Maybe String
    , actus :: Maybe XML
    }

toArray :: PlaygroundFiles -> Array NewGistFile
toArray { playground, marlowe, haskell, blockly, javascript, actus } =
  [ mkNewGistFile filenames.playground playground
  ]
    <> catMaybes
        [ mkNewGistFile filenames.marlowe <$> marlowe
        , mkNewGistFile filenames.haskell <$> haskell
        , mkNewGistFile filenames.blockly <$> blockly
        , mkNewGistFile filenames.javascript <$> javascript
        , mkNewGistFile filenames.actus <<< unwrap <$> actus
        ]

filenames ::
  { playground :: String
  , marlowe :: String
  , haskell :: String
  , blockly :: String
  , javascript :: String
  , actus :: String
  }
filenames =
  { playground: "playground.marlowe.json"
  , marlowe: "playground.marlowe"
  , haskell: "Main.hs"
  , blockly: "blockly.xml"
  , javascript: "playground.js"
  , actus: "actus.xml"
  }

isPlaygroundGist :: Gist -> Boolean
isPlaygroundGist = has (gistFiles <<< ix filenames.playground)

playgroundFiles :: Gist -> PlaygroundFiles
playgroundFiles gist =
  { playground: fromMaybe "{}" $ getFile filenames.playground
  , marlowe: getFile filenames.marlowe
  , haskell: getFile filenames.haskell
  , blockly: getFile filenames.blockly
  , javascript: getFile filenames.javascript
  , actus: wrap <$> getFile filenames.actus
  }
  where
  getFile name = view (gistFiles <<< ix name <<< gistFileContent) gist

fileExists :: String -> Gist -> Boolean
fileExists name gist = has (gistFiles <<< ix name) gist
