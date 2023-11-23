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
import Data.Text (Text)
import System.Environment (getArgs, getProgName)
import System.Exit
import Text.Printf (printf)

data ModelComponent = Cpu | Memory


-------------- Types representing cost mode entries and functions for JSON parsing ----------------

data LinearFunction =
    LinearFunction {intercept_ :: Integer, slope_ :: Integer}
                   deriving stock Show

instance FromJSON LinearFunction where
    parseJSON = withObject "Linear function" $ \obj ->
                LinearFunction <$> obj .: "intercept" <*> obj .: "slope"

{- | This type reflects what is actually in the JSON.  The stuff in
   CostingFun.Core and CostingFun.JSON is much more rigid, allowing parsing only
   for the model types applicable to the various ModelNArguments types; it also
   requires entries for everything in DefaultFun. Using the type defined here
   allows us to be more flexible and parse stuff that's not exactly what's
   expected in builtinCostModel.json.
-}
data Model
    = ConstantCost       Integer
    | AddedSizes         LinearFunction
    | MultipliedSizes    LinearFunction
    | MinSize            LinearFunction
    | MaxSize            LinearFunction
    | LinearCost         LinearFunction
    | LinearInX          LinearFunction
    | LinearInY          LinearFunction
    | LinearInZ          LinearFunction
    | SubtractedSizes    LinearFunction Integer
    -- ^ Linear model in x-y plus minimum value for the case x-y < 0.
    | ConstAboveDiagonal Integer Model
    | ConstBelowDiagonal Integer Model
    | LinearOnDiagonal   LinearFunction Integer
      -- ^ Linear model for x=y together with a constant for the case x!=y; we
      -- should probably allow a general model here.
      deriving stock Show

{- The JSON representation consists of a list of pairs of (type, arguments)
   values.  The "type" field corresponds to the possible constructors above, the
   "arguments" field contains the arguments for that particular constructor.

   The JSON format is a bit inconsistent, which adds some complexity.  For
   example, the "arguments" field is sometimes a constant, sometimes an object
   representing a linear function, and sometimes an object which contains the
   coefficients of a linear function together with some extra data. It would be
   nice to rationalise this a bit, but it may be too late to do that.
-}

instance FromJSON Model where
    parseJSON =
        withObject "Model" $
           \obj -> do
             ty   :: Text  <- obj .: "type"
             args :: Value <- obj .: "arguments"
             {- We always have an "arguments" field which is a Value.  Usually it's
                actually an Object (ie, a map) representing a linear function, but
                sometimes it contains other data, and in those cases we need to
                coerce it to an Object (with objOf) to extract the relevant date.
                We could do that once here and rely on laziness to save us in the
                cases when we don't have an Object, but that looks a bit misleading. -}
             case ty of
               "constant_cost"        -> ConstantCost          <$> parseJSON args
               "added_sizes"          -> AddedSizes            <$> parseJSON args
               "min_size"             -> MinSize               <$> parseJSON args
               "max_size"             -> MaxSize               <$> parseJSON args
               "multiplied_sizes"     -> MultipliedSizes       <$> parseJSON args
               "linear_cost"          -> LinearCost            <$> parseJSON args
               "linear_in_x"          -> LinearInX             <$> parseJSON args
               "linear_in_y"          -> LinearInY             <$> parseJSON args
               "linear_in_z"          -> LinearInZ             <$> parseJSON args
               "subtracted_sizes"     ->
                  SubtractedSizes       <$> parseJSON args <*> objOf args .: "minimum"
               "const_above_diagonal" ->
                  ConstAboveDiagonal    <$> objOf args .: "constant" <*> objOf args .: "model"
               "const_below_diagonal" ->
                  ConstBelowDiagonal    <$> objOf args .: "constant" <*> objOf args .: "model"
               "linear_on_diagonal"   ->
                  LinearOnDiagonal      <$> parseJSON args <*> objOf args .: "constant"
               _                      -> errorWithoutStackTrace $ "Unknown model type " ++ show ty

               where objOf (Object o) = o
                     objOf _          =
                      errorWithoutStackTrace "Failed to get Object while parsing \"arguments\""

{- | A CPU usage modelling function and a memory usage modelling function bundled
   together -}
data CpuAndMemoryModel = CpuAndMemoryModel {cpuModel :: Model, memoryModel :: Model}
              deriving stock Show

instance FromJSON CpuAndMemoryModel where
    parseJSON = withObject "CpuAndMemoryModel" $ \obj ->
                CpuAndMemoryModel <$> obj .: "cpu" <*> obj .: "memory"


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

renderModel :: Model -> [String]
renderModel =
    \case
     ConstantCost       n   -> [ printf "%d" n ]
     AddedSizes         f   -> [ renderLinearFunction f "(x+y)" ]
     MultipliedSizes    f   -> [ renderLinearFunction f "(x*y)" ]
     MinSize            f   -> [ renderLinearFunction f "min(x,y)" ]
     MaxSize            f   -> [ renderLinearFunction f "max(x,y)" ]
     LinearCost         f   -> [ renderLinearFunction f "x" ]
     LinearInX          f   -> [ renderLinearFunction f "x" ]
     LinearInY          f   -> [ renderLinearFunction f "y" ]
     LinearInZ          f   -> [ renderLinearFunction f "z" ]
     SubtractedSizes    l c -> [ "if x>y"
                               , printf "then %s" $ renderLinearFunction l "(x-y)"
                               , printf "else %d" c
                               ]
     ConstAboveDiagonal c m -> [ "if x>y"
                               , printf "then %s" $ intercalate "\n" (renderModel m)
                               , printf "else %d" c
                               ]
     ConstBelowDiagonal c m -> [ "if x<y"
                               , printf "then %s" $ intercalate "\n" (renderModel m)
                               , printf "else %d" c
                               ]
     LinearOnDiagonal   f c -> [ "if x==y"
                               , printf "then %s" $ renderLinearFunction f "x"
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
  printf "The variables x, y, z, etc. represent the *sizes* of the builtin's arguments.\n"
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
                      | elem arg ["-c", "--cpu"]     = parse rest (Cpu, input)
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

