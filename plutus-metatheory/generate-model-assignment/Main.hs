{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE OverloadedStrings #-}

{- | A program to parse a JSON representation of costing functions for Plutus Core
   builtins and print it in readable form. -}
module Main where

--import Paths_plutus_core

import Data.Aeson
import Data.Aeson.Key as Key (toString)
import Data.Aeson.KeyMap qualified as KeyMap
import Data.ByteString.Lazy as BSL (getContents, readFile)
import Data.List (intercalate)
import Data.Text (Text)
import System.Environment (getArgs, getProgName)
import System.Exit
import Text.Printf (printf)

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

-- | Print a linear function
renderLinearFunction :: LinearFunction -> String
renderLinearFunction (LinearFunction intercept slope) =
   printf "%d %d" intercept slope

renderModel :: Model -> String
renderModel =
    \case
     ConstantCost       n   -> printf "constantCost %d" n
     AddedSizes         f   -> printf "addedSizes %s" (renderLinearFunction f)
     MultipliedSizes    f   -> printf "multipliedSizes %s" (renderLinearFunction f)
     MinSize            f   -> printf "minSize %s" (renderLinearFunction f)
     MaxSize            f   -> printf "maxSize %s" (renderLinearFunction f)
     LinearCost         f   -> printf "linearCostIn zero %s" (renderLinearFunction f)
     LinearInX          f   -> printf "linearCostIn zero %s" (renderLinearFunction f)
     LinearInY          f   ->
      printf "linearCostIn (suc zero) %s" (renderLinearFunction f)
     LinearInZ          f   ->
      printf "linearCostIn (suc (suc zero)) %s" (renderLinearFunction f)
     SubtractedSizes    l c ->
       printf "twoArgumentsSubtractedSizes %s %d" (renderLinearFunction l) c
     ConstAboveDiagonal c m ->
       printf "twoArgumentsConstAboveDiagonal %d (%s)" c (renderModel m)
     ConstBelowDiagonal c m ->
       printf "twoArgumentsConstBelowDiagonal %d (%s)" c (renderModel m)
     LinearOnDiagonal   f c ->
       printf "twoArgumentsLinearOnDiagonal %d %s" c (renderLinearFunction f)

-- | Take a list of strings and print them line by line.
printListIndented :: Int -> [String] -> IO ()
printListIndented width =  mapM_ (\s -> printf "%s%s\n" spaces s)
          where spaces = replicate width ' '

{- | Print a Builtin replacing the '_' with '-'
 (underscores in Agda have a different meaning) -}
printBuiltin :: Key -> String
printBuiltin = map (\c -> if c == '_' then '-' else c). Key.toString

-- | Print the case of a function `assignModel` for a given Builtin (the Key below).
printModel :: (Key, CpuAndMemoryModel) -> IO ()
printModel (name, CpuAndMemoryModel cpu mem) = do
    printf "assignModel %s =\n" (printBuiltin name)
    printListIndented 4 [ "record { costingCPU = " ++ renderModel cpu
                        , "       ; costingMem = " ++ renderModel mem ++ " }"]

agdaHeader :: String
agdaHeader = "-- Assignment of models to Builtins\n\n"
         ++ "module Cost.BuiltinModelAssignment where\n\n"
         ++ "open import Data.Fin using (suc;zero)\n"
         ++ "open import Builtin using (Builtin;arity)\n"
         ++ "open Builtin.Builtin\n"
         ++ "open import Cost.Model using (BuiltinModel;CostingModel;costingCPU;costingMem)\n"
         ++ "open CostingModel\n\n"
         ++ "assignModel : (b : Builtin) → BuiltinModel (arity b)"

---------------- Command line processing ----------------

usage :: FilePath -> IO a
usage defaultCostModelPath = do
  prog <- getProgName
  printf "Usage: %s [<filename>]\n" prog
  printf "\n"
  printf "Generate an Agda module defining an assignment of models to builtins.\n"
  printf "Input is read from stdin if no file is given and --default is not specified.\n"
  printf "\n"
  printf "Options (later options take precedence over earlier ones):\n"
  printf "   -d, --default: print the contents of the default cost model in\n"
  printf "      %s\n" defaultCostModelPath
  printf "   <filename>: read and print the cost model in the given file\n"
  exitSuccess

parseArgs :: [String] -> FilePath -> IO (Maybe String)
parseArgs args defaultCostModelPath =
  parse args Nothing
    where parse [] result = pure result
          parse (arg:rest) input =
              case arg of
                []    -> errorWithoutStackTrace "Empty argument"
                '-':_ -> parseOption arg rest input
                _     -> parse rest (Just arg)
          parseOption arg rest input
                      | elem arg ["-d", "--default"] =
                        parse rest (Just defaultCostModelPath)
                      | elem arg ["-h", "--help"] = usage defaultCostModelPath
                      | otherwise =
                        printf "Error: unknown option %s\n" arg >> usage defaultCostModelPath

main :: IO ()
main = do
  args <- getArgs
--  defaultCostModelPath <- getDataFileName "cost-model/data/builtinCostModel.json"
  let defaultCostModelPath = "cost-model/data/builtinCostModel.json"
  input <- parseArgs args defaultCostModelPath
  bytes <- maybe BSL.getContents BSL.readFile input
  case eitherDecode bytes :: Either String (KeyMap.KeyMap CpuAndMemoryModel) of
    Left err -> putStrLn err
    Right m  -> putStrLn agdaHeader >> mapM_ printModel (KeyMap.toList m)

