{-# LANGUAGE ImpredicativeTypes #-}
module Mode.ListExamples
    ( runListExamples
    ) where

import Common
import AnyProgram.Example

runListExamples :: IO ()
runListExamples = do
    printE "List of available example names:"
    -- the names go to stdout
    putStr $ unlines $
        (fst <$> termExamples) ++ (fst <$> typeExamples)
    printE "Use --example=NAME to include them as input."
