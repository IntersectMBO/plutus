module System.Console.SimpleReadline(
  getInputLine,
  getInputLineHist,
  getInputLineHistComp,
  ) where

getInputLine :: String -> IO (Maybe String)
getInputLine _ = return Nothing

getInputLineHist :: FilePath -> String -> IO (Maybe String)
getInputLineHist _ _ = return Nothing

getInputLineHistComp :: ((String, String) -> IO [String]) -> FilePath -> String -> IO (Maybe String)
getInputLineHistComp _ _ _ = return Nothing
