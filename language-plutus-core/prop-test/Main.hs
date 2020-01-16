{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import Control.Search (search)
import Control.Monad (forM_)
import Control.Monad.State
import Language.PlutusCore.Name
import Language.PlutusCore.Pretty
import Language.PlutusCore.Type.Gen
import qualified Data.Text as T


-- |Stream of names x0, x1, x2, ..
exes :: [Name ()]
exes = nameStream [ "x" <> T.pack (show n) | n <- [0 :: Integer ..] ]


-- |Convert a stream of text strings to a stream of PLC names.
nameStream :: [T.Text] -> [Name ()]
nameStream strs = evalState (traverse newName strs) emptyIdentifierState
  where
    newName str = do
      uniq <- newIdentifier str
      return (Name () str uniq)


main :: IO ()
main = do
  let kG = TypeG
  tyGs <- search 10 (checkClosedTypeG kG)
  forM_ tyGs $ \tyG -> do
    let ty = toClosedType exes kG tyG
    putStrLn (prettyPlcDefString ty)
