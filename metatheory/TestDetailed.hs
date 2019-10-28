module TestDetailed where
import           Control.Exception
import           GHC.IO.Handle
import           System.Directory
import           System.Environment
import           System.Exit
import           System.IO
import           System.Process

import           Distribution.TestSuite

import qualified MAlonzo.Code.Main      as M

-- this function is based on this stackoverflow answer:
-- https://stackoverflow.com/a/9664017

catchOutput :: IO () -> IO String
catchOutput act = do
  tmpD <- getTemporaryDirectory
  (tmpFP, tmpH) <- openTempFile tmpD "stdout"
  stdoutDup <- hDuplicate stdout
  hDuplicateTo tmpH stdout
  hClose tmpH
  act
  hDuplicateTo stdoutDup stdout
  str <- readFile tmpFP
  removeFile tmpFP
  return str

compareResult :: String -> IO Progress
compareResult test = do
  example <- readProcess "plc" ["example","-s",test] []
  writeFile "tmp" example
  putStrLn $ "test: " ++ test
  plcOutput <- readProcess "plc" ["evaluate","--file","tmp"] []
  plcAgdaOutput <- catchOutput $ catch
    (withArgs ["evaluate","--file","tmp"]  M.main)
    (\ e -> case e of
        ExitFailure _ -> exitFailure
        ExitSuccess   -> return ())
  return $ Finished $ if plcOutput == plcAgdaOutput then Pass else Fail "it failed!"

testNames = ["succInteger"
        ,"unitval"
        ,"true"
        ,"false"
        ,"churchZero"
        ,"churchSucc"
        ,"overapplication"
        ,"factorial"
        ,"fibonacci"
        ,"NatRoundTrip"
        ,"ListSum"
        ,"IfIntegers"
        ,"ApplyAdd1"
        ,"ApplyAdd2"
        ]

mkTest :: String -> TestInstance
mkTest s = TestInstance
        { run = compareResult s
        , name = s
        , tags = []
        , options = []
        , setOption = \_ _ -> Right (mkTest s)
        }

tests :: IO [Test]
tests = --return [ Test succeeds ] -- , Test fails ]
  return $ map Test (map mkTest testNames)
  where
    fails = TestInstance
        { run = return $ Finished $ Fail "Always fails!"
        , name = "fails"
        , tags = []
        , options = []
        , setOption = \_ _ -> Right fails
        }
