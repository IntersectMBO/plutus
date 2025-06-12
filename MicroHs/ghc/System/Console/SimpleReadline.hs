module System.Console.SimpleReadline(
--  getInputLine,
  getInputLineHist,
  getInputLineHistComp,
  ) where
import System.Console.Haskeline qualified as H
import System.Console.Haskeline hiding (getInputLine)

{-
getInputLine :: String -> IO (Maybe String)
getInputLine prompt =
  runInputT defaultSettings (H.getInputLine prompt)
-}

getInputLineHist :: FilePath -> String -> IO (Maybe String)
getInputLineHist hist prompt =
  runInputT settings (H.getInputLine prompt)
  where settings = defaultSettings { historyFile = Just hist }

getInputLineHistComp :: ((String, String) -> IO [String]) -> FilePath -> String -> IO (Maybe String)
getInputLineHistComp comp hist prompt =
  runInputT settings (H.getInputLine prompt)
  where settings = setComplete hcomp $ defaultSettings { historyFile = Just hist }
        hcomp :: CompletionFunc IO
        hcomp pp@(pre, _) = do
          alts <- comp pp
          return (pre, map (\ s -> Completion s s False) alts)
