{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE OverloadedStrings #-}


{- | A program to parse a JSON representation of costing functions for Plutus Core
   builtins and print it in readable form. -}
module Main where

import Paths_plutus_core

import Data.Aeson
import Data.Aeson.Key as Key (toString)
import Data.Aeson.KeyMap qualified as KeyMap
import Data.ByteString.Lazy as BSL (getContents, readFile)
import Data.List (intercalate)
import System.Environment (getArgs, getProgName)
import System.Exit
import Text.Printf (printf)

import PlutusCore.Evaluation.Machine.CostingFun.SimpleJSON

data ModelComponent = Cpu | Memory

---------------- Printing cost models  ----------------

-- | Print a linear function in readable form.  The string argument is
-- supposed to represent the input to the function: x, y, y+z, etc.
renderLinearFunction :: LinearFunction -> String -> String
renderLinearFunction (LinearFunction intercept slope) var =
    if intercept == 0 then stringOfMonomial slope var
    else printf "%d + %s" intercept (stringOfMonomial slope var)
        where stringOfMonomial s v =
                  if s == 1 then unparen v  -- Just so we don't get things like 5 + (x+y).
                  else if s == -1 then "-" ++ v
                  else printf "%d*%s" s v
                  -- Print the slope even if it's zero, so we know the
                  -- function's not constant.
              unparen v = if v /= "" && head v == '(' && last v == ')'
                          then tail $ init v
                          else v
renderOneVariablrQuadraticFunction
  :: OneVariableQuadraticFunction
  -> String
  -> String
renderOneVariablrQuadraticFunction
  (OneVariableQuadraticFunction c0 c1 c2) var =
    printf "%d + %d*%s + %d*%s^2" c0 c1 var c2 var

renderTwoVariableQuadraticFunction
  :: TwoVariableQuadraticFunction
  -> String
  -> String
  -> String
renderTwoVariableQuadraticFunction
  (TwoVariableQuadraticFunction c00 c10 c01 c20 c11 c02) var1 var2 =
    printf "%d + %d*%s + %d*s + %d*%s^2 + %d*%s*%s + %d*%s^2"
    c00 c10 var1 c01 var2 c20 var1 c11 var1 var2 c02 var2

renderModel :: Model -> [String]
renderModel =
    \case
     ConstantCost          n   -> [ printf "%d" n ]
     AddedSizes            f   -> [ renderLinearFunction f "(x+y)" ]
     MultipliedSizes       f   -> [ renderLinearFunction f "(x*y)" ]
     MinSize               f   -> [ renderLinearFunction f "min(x,y)" ]
     MaxSize               f   -> [ renderLinearFunction f "max(x,y)" ]
     LinearInX             f   -> [ renderLinearFunction f "x" ]
     LinearInY             f   -> [ renderLinearFunction f "y" ]
     LinearInZ             f   -> [ renderLinearFunction f "z" ]
     QuadraticInY          f   -> [ renderOneVariablrQuadraticFunction f "y" ]
     QuadraticInZ          f   -> [ renderOneVariablrQuadraticFunction f "z" ]
     QuadraticInXAndY      f   -> [ renderTwoVariableQuadraticFunction f "x" "y" ]
     LiteralInYOrLinearInZ f -> [ "if y==0"
                                  , printf "then %s" $ renderLinearFunction f "z"
                                  , printf "else y bytes"
                                ]  -- This is only used for the memory usage of
                                   -- `integerToByteString` at the moment, so
                                   -- this makes sense.
     SubtractedSizes       l c -> [ "if x>y"
                                  , printf "then %s" $ renderLinearFunction l "(x-y)"
                                  , printf "else %d" c
                               ]
     ConstAboveDiagonal    c m -> [ "if x>y"
                                  , printf "then %s" $ intercalate "\n" (renderModel m)
                                  , printf "else %d" c
                                  ]
     ConstBelowDiagonal    c m -> [ "if x<y"
                                  , printf "then %s" $ intercalate "\n" (renderModel m)
                                  , printf "else %d" c
                                  ]
     ConstOffDiagonal      c m -> [ "if x==y"
                                  , printf "then %s" $ intercalate "\n" (renderModel m)
                                  , printf "else %d" c
                                  ]
     -- ^ We're not properly indenting submodels in the above/below diagonal
     -- cases, but at present our submodels all fit on one line (eg, constant or
     -- linear).  It seems improbable that we'd ever have a submodel that
     -- required more than one line because then we'd be dividing the plane up
     -- into more than two regions.

-- | Take a list of strings and print them line by line, the first with no extra
-- spaces then the rest preceded by `width` spaces. The assumption is that we'll
-- already have printed the first part of the first line.
printListIndented :: Int -> [String] -> IO ()
printListIndented width l =
    case l of
      [] -> pure ()
      first:rest -> do
          printf "%s\n" first
          mapM_ (\s -> printf "%s%s\n" spaces s)  rest
          where spaces = take width $ repeat ' '

-- | Print a the name of a builtin (the Key below) and then a possibly
-- multi-line representation of the model, alinged so that each line of the
-- model has the same indentation.
printModel :: ModelComponent -> Int -> (Key, CpuAndMemoryModel) -> IO ()
printModel component width (name, CpuAndMemoryModel cpu mem) = do
    let model = case component of {Cpu -> cpu; Memory -> mem}
    printf "%-*s: " width (Key.toString name)
    printListIndented (width+2) (renderModel model)  -- +2 to account for ": " after builtin name


---------------- Command line processing ----------------

usage :: FilePath -> IO a
usage defaultCostModelPath = do
  prog <- getProgName
  printf "Usage: %s [-c|--cpu|-m|--mem|--memory] [-d|--default] [<filename>]\n" prog
  printf "\n"
  printf "Print a JSON cost model file in readable form.\n"
  printf "The variables x, y, z, etc. represent the *sizes* of the builtin's arguments\n"
  printf "unless explicitly specified otherwise (eg \"z bytes\").\n"
  printf "Input is read from stdin if no file is given and --default is not specified.\n"
  printf "\n"
  printf "Options (later options take precedence over earlier ones):\n"
  printf "   -c, --cpu (default):  print the CPU costing functions for each built-in function\n"
  printf "   -m, --mem --memory:  print the memory costing functions for each built-in function\n"
  printf "   -d, --default: print the contents of the default cost model in\n"
  printf "      %s\n" defaultCostModelPath
  printf "   <filename>: read and print the cost model in the given file\n"
  exitSuccess

parseArgs :: [String] -> FilePath -> IO (ModelComponent, Maybe String)
parseArgs args defaultCostModelPath =
  parse args (Cpu, Nothing)
    where parse [] result = pure result
          parse (arg:rest) (component, input) =
              case arg of
                []    -> errorWithoutStackTrace "Empty argument"
                '-':_ -> parseOption arg rest (component, input)
                _     -> parse rest (component, Just arg)
          parseOption arg rest (component, input)
                      | elem arg ["-d", "--default"] =
                        parse rest (component, Just defaultCostModelPath)
                      | elem arg ["-c", "--cpu"] = parse rest (Cpu, input)
                      | elem arg ["-m", "--mem", "--memory"] = parse rest (Memory, input)
                      | elem arg ["-h", "--help"] = usage defaultCostModelPath
                      | otherwise =
                        printf "Error: unknown option %s\n" arg >> usage defaultCostModelPath

main :: IO ()
main = do
  args <- getArgs
  defaultCostModelPath <- getDataFileName "cost-model/data/builtinCostModel.json"
  (component, input) <- parseArgs args defaultCostModelPath
  bytes <- case input of
             Nothing   -> BSL.getContents  -- Read from stdin
             Just file -> BSL.readFile file
  case eitherDecode bytes :: Either String (KeyMap.KeyMap CpuAndMemoryModel) of
    Left err -> putStrLn err
    Right m  ->
       let  l = KeyMap.toList m
            width = 1 + (maximum $ fmap (length . toString . fst) l)
       -- ^ Width for indentation, leaving at least one space after the name of each builtin.
       -- We want all the costing function to be aligned with each other.
       in mapM_ (printModel component width) l
