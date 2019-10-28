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

compareResult :: String -> String -> IO Progress
compareResult mode test = do
  example <- readProcess "plc" ["example","-s",test] []
  writeFile "tmp" example
  putStrLn $ "test: " ++ test
  plcOutput <- readProcess "plc" [mode,"--file","tmp"] []
  plcAgdaOutput <- catchOutput $ catch
    (withArgs [mode,"--file","tmp"]  M.main)
    (\ e -> case e of
        ExitFailure _ -> exitFailure
        ExitSuccess   -> return ())
  return $ Finished $ if plcOutput == plcAgdaOutput then Pass else Fail "it failed!"

evalTestNames = ["succInteger"
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

tcTestNames  = ["succInteger"
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

mkTest :: String -> String -> TestInstance
mkTest mode test = TestInstance
        { run = compareResult mode test
        , name = mode ++ " " ++ test
        , tags = []
        , options = []
        , setOption = \_ _ -> Right (mkTest mode test)
        }

tests :: IO [Test]
tests = do --return [ Test succeeds ] -- , Test fails ]
  return $ map Test
    (map (mkTest "evaluate") evalTestNames
     ++
     map (mkTest "typecheck") tcTestNames)
  where
    fails = TestInstance
        { run = return $ Finished $ Fail "Always fails!"
        , name = "fails"
        , tags = []
        , options = []
        , setOption = \_ _ -> Right fails
        }
