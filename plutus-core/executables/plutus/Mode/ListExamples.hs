{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE ImpredicativeTypes #-}

module Mode.ListExamples
  ( runListExamples
  ) where

import AnyProgram.Example
import Common
import GetOpt

runListExamples
  :: (?opts :: Opts)
  => IO ()
runListExamples = do
  printE "List of available example names:"
  -- the names go to stdout
  putStr $
    unlines $
      (fst <$> termExamples) ++ (fst <$> typeExamples)
  printE "Use --example=NAME to include them as input."
