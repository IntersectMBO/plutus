module Main where

import System.Exit (exitFailure)
import System.Process

main = do
  callCommand "plc example -s succInteger | plc-agda evaluate --stdin"
  callCommand "plc example -s unitval | plc-agda evaluate --stdin"
  callCommand "plc example -s true | plc-agda evaluate --stdin"
  callCommand "plc example -s false | plc-agda evaluate --stdin"
  callCommand "plc example -s churchZero | plc-agda evaluate --stdin"
  callCommand "plc example -s churchSucc | plc-agda evaluate --stdin"
  callCommand "plc example -s overapplication | plc-agda evaluate --stdin"
  callCommand "plc example -s factorial | plc-agda evaluate --stdin"
  callCommand "plc example -s fibonacci | plc-agda evaluate --stdin"
  callCommand "plc example -s NatRoundTrip | plc-agda evaluate --stdin"
  callCommand "plc example -s ListSum | plc-agda evaluate --stdin"
  callCommand "plc example -s IfIntegers | plc-agda evaluate --stdin"
  callCommand "plc example -s ApplyAdd1 | plc-agda evaluate --stdin"
  callCommand "plc example -s ApplyAdd2 | plc-agda evaluate --stdin"
  callCommand "plc example -s DivideByZero | plc-agda evaluate --stdin"
