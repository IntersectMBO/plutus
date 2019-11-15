module Marlowe.Gists
  ( mkNewGist
  , gistSourceFilename
  , playgroundGistFile
  ) where

import Data.Array (catMaybes)
import Data.Array as Array
import Data.Maybe (Maybe(..))
import Data.Newtype (unwrap)
import Gist (NewGist(NewGist), NewGistFile(NewGistFile), Gist, GistFile)
import Gists (firstMatch)
import Language.Haskell.Interpreter (SourceCode)
import Prelude (($), (<$>), (<<<))

mkNewGist ::
  Maybe SourceCode ->
  Maybe NewGist
mkNewGist source =
  if Array.null gistFiles then
    Nothing
  else
    Just
      $ NewGist
          { _newGistDescription: "Marlowe Smart Contract"
          , _newGistPublic: true
          , _newGistFiles: gistFiles
          }
  where
  gistFiles =
    catMaybes
      [ mkNewGistFile gistSourceFilename <<< unwrap <$> source
      ]

  mkNewGistFile _newGistFilename _newGistFileContent =
    NewGistFile
      { _newGistFilename
      , _newGistFileContent
      }

gistSourceFilename :: String
gistSourceFilename = "Marlowe.hs"

playgroundGistFile :: Gist -> Maybe GistFile
playgroundGistFile = firstMatch gistSourceFilename
