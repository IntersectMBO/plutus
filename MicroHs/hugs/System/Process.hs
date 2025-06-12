module System.Process(callCommand) where
import System.Cmd
import System.Exit

callCommand :: String -> IO ()
callCommand cmd = do
  rc <- system cmd
  case rc of
    ExitSuccess -> return ()
    ExitFailure _ -> error $ "callCommand: failed " ++ show rc ++ ", " ++ show cmd
