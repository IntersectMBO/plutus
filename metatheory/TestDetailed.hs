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
  plcOutput <- readProcess "plc" [mode,"--input","tmp"] []
  plcAgdaOutput <- catchOutput $ catch
    (withArgs [mode,"--file","tmp"]  M.main)
    (\ e -> case e of
        ExitFailure _ -> exitFailure
        ExitSuccess   -> return ())
  return $ Finished $ if eq (C.pack plcOutput) (C.pack plcAgdaOutput) then Pass else Fail $ "plc: '" ++ plcOutput ++ "' " ++ "plc-agda: '" ++ plcAgdaOutput ++ "'"

compareResultMode :: String -> String -> (C.ByteString -> C.ByteString -> Bool) -> String -> IO Progress
compareResultMode mode1 mode2 eq test = do
  example <- readProcess "plc" ["example","-s",test] []
  writeFile "tmp" example
  putStrLn $ "test: " ++ test
  plcAgdaOutput1 <- catchOutput $ catch
    (withArgs ["evaluate","--file","tmp","--mode",mode1]  M.main)
    (\ e -> case e of
        ExitFailure _ -> exitFailure
        ExitSuccess   -> return ())
  plcAgdaOutput2 <- catchOutput $ catch
    (withArgs ["evaluate","--file","tmp","--mode",mode2]  M.main)
    (\ e -> case e of
        ExitFailure _ -> exitFailure
        ExitSuccess   -> return ())
  return $ Finished $ if eq (C.pack plcAgdaOutput1) (C.pack plcAgdaOutput2) then Pass else Fail $ mode1 ++ ": '" ++ plcAgdaOutput1 ++ "' " ++ mode2 ++ ": '" ++ plcAgdaOutput2 ++ "'"

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
-- test plc against plc-agda
mkTest :: (C.ByteString -> C.ByteString -> Bool) -> String -> String -> TestInstance
mkTest eq mode test = TestInstance
        { run = compareResult eq mode test
        , name = mode ++ " " ++ test
        , tags = []
        , options = []
        , setOption = \_ _ -> Right (mkTest eq mode test)
        }

-- test different plc-agda modes against each other
mkTestMode :: String -> String -> (C.ByteString -> C.ByteString -> Bool) -> String -> TestInstance
mkTestMode mode1 mode2 eq test = TestInstance
        { run = compareResultMode mode1 mode2 eq test
        , name = test
        , tags = []
        , options = []
        , setOption = \_ _ -> Right (mkTestMode mode1 mode2 eq test)
        }

tests :: IO [Test]
tests = do --return [ Test succeeds ] -- , Test fails ]
  return $ map Test $
    map (mkTest M.alphaTm "evaluate") testNames
     ++
    map (mkTestMode "L" "CK" M.alphaTm) testNames
     ++
    map (mkTestMode "CK" "TCK" M.alphaTm) (tail testNames)
    -- ^ skip "succInteger" to avoid sat/unsat eta expansion differences
     ++
    map (mkTestMode "TCK" "TCEKV" M.alphaTm) testNames
     ++
    map (mkTestMode "TCEKV" "TCEKC" M.alphaTm) testNames
     ++
    map (mkTest M.alphaTy "typecheck") testNames
  where
    fails = TestInstance
        { run = return $ Finished $ Fail "Always fails!"
        , name = "fails"
        , tags = []
        , options = []
        , setOption = \_ _ -> Right fails
        }
