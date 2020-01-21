module TestDetailed where
import           Control.Exception
import qualified Data.Text                  as T
import           GHC.IO.Handle
import           System.Directory
import           System.Environment
import           System.Exit
import           System.IO
import           System.Process

import           Distribution.TestSuite

import qualified MAlonzo.Code.Main          as M
import qualified MAlonzo.Code.Raw           as R

import qualified Data.ByteString.Lazy.Char8 as C

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

compareResult :: (C.ByteString -> C.ByteString -> Bool) -> String -> String -> IO Progress
compareResult eq mode test = do
  example <- readProcess "plc" ["example","-s",test] []
  writeFile "tmp" example
  putStrLn $ "test: " ++ test
  plcOutput <- readProcess "plc" [mode,"--file","tmp"] []
  plcAgdaOutput <- catchOutput $ catch
    (withArgs [mode,"--file","tmp"]  M.main)
    (\ e -> case e of
        ExitFailure _ -> exitFailure
        ExitSuccess   -> return ())
  return $ Finished $ if eq (C.pack plcOutput) (C.pack plcAgdaOutput) then Pass else Fail "it failed!"

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

mkTest :: (C.ByteString -> C.ByteString -> Bool) -> String -> String -> TestInstance
mkTest eq mode test = TestInstance
        { run = compareResult eq mode test
        , name = mode ++ " " ++ test
        , tags = []
        , options = []
        , setOption = \_ _ -> Right (mkTest eq mode test)
        }
tests :: IO [Test]
tests = do --return [ Test succeeds ] -- , Test fails ]
  return $ map Test
    (map (mkTest M.alphaTm "evaluate") evalTestNames
     ++
     map (mkTest M.alphaTy "typecheck") tcTestNames)
  where
    fails = TestInstance
        { run = return $ Finished $ Fail "Always fails!"
        , name = "fails"
        , tags = []
        , options = []
        , setOption = \_ _ -> Right fails
        }
