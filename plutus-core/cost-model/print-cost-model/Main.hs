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

-- Print a monomial like 5*x or 11*max(x,y)
stringOfMonomial :: Integer -> String -> String
stringOfMonomial s v =
  if s == 1 then unparen v  -- Just so we don't get things like 5 + (x+y).
  else if s == -1 then "-" ++ v
       else printf "%d*%s" s v
            -- Print the slope even if it's zero, so we know the
            -- function's not constant.
  where unparen w =
          if w /= "" && head w == '(' && last w == ')'
          then tail $ init w
          else w

-- | Print a linear function in readable form.  The string argument is
-- supposed to represent the input to the function: x, y, y+z, etc.
renderLinearFunction :: LinearFunction -> String -> String
renderLinearFunction (LinearFunction intercept slope) var =
    if intercept == 0 then stringOfMonomial slope var
    else printf "%d + %s" intercept (stringOfMonomial slope var)

renderTwoVariableLinearFunction :: TwoVariableLinearFunction -> String -> String -> String
renderTwoVariableLinearFunction (TwoVariableLinearFunction intercept slope1 slope2) var1 var2 =
    if intercept == 0
    then stringOfMonomial slope1 var1 ++ " + " ++ stringOfMonomial slope2 var2
    else printf "%d + %s + %s"
      intercept
      (stringOfMonomial slope1 var1)
      (stringOfMonomial slope2 var2)

renderOneVariableQuadraticFunction
  :: OneVariableQuadraticFunction
  -> String
  -> String
renderOneVariableQuadraticFunction
  (OneVariableQuadraticFunction c0 c1 c2) var =
    printf "%d + %d*%s + %d*%s^2" c0 c1 var c2 var

renderTwoVariableQuadraticFunction
  :: TwoVariableQuadraticFunction
  -> String
  -> String
  -> String
renderTwoVariableQuadraticFunction
  (TwoVariableQuadraticFunction minVal c00 c10 c01 c20 c11 c02) var1 var2 =
    printf "max(%d, %d + %d*%s + %d*%s + %d*%s^2 + %d*%s*%s + %d*%s^2)"
    minVal c00 c10 var1 c01 var2 c20 var1 c11 var1 var2 c02 var2

renderSquareOfTwoVariableSumFunction
  :: SquareOfTwoVariableSumFunction
  -> String
  -> String
  -> String
renderSquareOfTwoVariableSumFunction
  (SquareOfTwoVariableSumFunction _c00 _c11) _var1 _var2 = "sq"

renderExpModCostingFunction
  :: ExpModCostingFunction
  -> String
  -> String
  -> String
renderExpModCostingFunction
  (ExpModCostingFunction c00 c11 c12) var1 var2 =
    printf "%d + %d*%s*%s + %d*%s*%s^2"
    c00 c11 var1 var2 c12 var1 var2

-- FIXME.  This is arguably slightly incorrect because some of the arguments are
-- wrapped in newtypes that change the memory usage instance of their content
-- and this isn't reflected in the output.  We're able to fix this for
-- LiteralInYOrLinearInZ since we can tell from the constructor that the second
-- argument is wrapped, but this doesn't work for `replicateByte`, where the
-- replication count is wrapped in NumBytesCostedAsNumWords and we don't see that
-- here.  We should really print "x bytes" instead of just "x", but to fix that
-- we'd need access to the signatures of the builtins here as well.  Maybe it
-- could be argued that the user should be aware of the wrappings and interpret
-- the output accordingly, but it would be helpful to make it explicit.
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
     LinearInW             f   -> [ renderLinearFunction f "w" ]
     QuadraticInY          f   -> [ renderOneVariableQuadraticFunction f "y" ]
     QuadraticInZ          f   -> [ renderOneVariableQuadraticFunction f "z" ]
     QuadraticInXAndY      f   -> [ renderTwoVariableQuadraticFunction f "x" "y" ]
     SquareOfSum           f   -> [ renderSquareOfTwoVariableSumFunction f "x" "y" ]
     ExpModCost            f   -> [ renderExpModCostingFunction f "y" "z" ]
     LinearInMaxYZ         f   -> [ renderLinearFunction f "max(y,z)" ]
     LinearInYAndZ         f   -> [ renderTwoVariableLinearFunction f "y" "z" ]
     LiteralInYOrLinearInZ f -> [ "if y==0"
                                  , printf "then %s" $ renderLinearFunction f "z"
                                  , printf "else y bytes"
                                ]  -- This is only used for the memory usage of
                                   -- `integerToByteString` at the moment, so
                                   -- this makes sense.
     SubtractedSizes       l c -> [ renderLinearFunction l $ printf "max(x-y,%d)" c
                                  ]
     ConstAboveDiagonal    c m -> [ "if x<y"
                                  , printf "then %d" c
                                  , printf "else %s" $ intercalate "\n" (renderModel m)
                                  ]
     ConstBelowDiagonal    c m -> [ "if x>y"
                                  , printf "then %d" c
                                  , printf "else %s" $ intercalate "\n" (renderModel m)
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

-- The names of the semantic variants.  If X is a semantic variant and you pass
-- -X on the command line then the program looks for a cost model file called
-- builtinCostModelX.json in the data directory and prints its contents.  The -d
-- option prints the cost model file (if any) corresponding to the final element
-- in the list.
semvars :: [String]
semvars = ["A", "B", "C"]

semvarOptions :: [String]
semvarOptions = fmap ('-':) semvars

usage :: [String] -> IO a
usage paths = do
  let semvarInfo = printf "[%s]" (intercalate "|" semvarOptions) :: String
  prog <- getProgName
  printf "Usage: %s [-c|--cpu|-m|--mem|--memory] [-d|--default] [<filename>] %s\n" prog semvarInfo
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
  printf "      %s\n" (last paths)
  printf "   <filename>: read and print the cost model in the given file\n"
  printf "   %s: read and print out the cost model for the given semantics variant\n"
             (intercalate "," semvarOptions)
  exitSuccess

parseArgs :: [String] -> IO (ModelComponent, Maybe String)
parseArgs args = do
  let prefix = "cost-model/data/builtinCostModel"
      extension = ".json"
  paths <- mapM (\x -> getDataFileName (prefix ++ x ++ extension)) semvars
  let parse [] result = pure result
      parse (arg:rest) (component, input) =
        case arg of
          []    -> errorWithoutStackTrace "Empty argument"
          '-':_ -> parseOption arg rest (component, input)
          _     -> parse rest (component, Just arg)
      parseOption arg rest (component, input)
        | Just path <- lookup arg $ zip semvarOptions paths =
            parse rest (component, Just path)
        | elem arg ["-d", "--default"] =
          parse rest (component, Just $ last paths)
        | elem arg ["-c", "--cpu"] = parse rest (Cpu, input)
        | elem arg ["-m", "--mem", "--memory"] = parse rest (Memory, input)
        | elem arg ["-h", "--help"] = usage paths
        | otherwise =
            printf "Error: unknown option %s\n" arg >> usage paths
  parse args (Cpu, Nothing)

main :: IO ()
main = do
  args <- getArgs
  (component, input) <- parseArgs args
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
