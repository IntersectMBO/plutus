{-# LANGUAGE OverloadedStrings #-}

{- | A program to parse a JSON representation of costing functions for Plutus Core
   builtins and generate an Agda module with a function that assigns builtins to models -}
module Cost.JSON where

import Data.Aeson
import Data.Aeson.Key as Key (toText)
import Data.Aeson.KeyMap qualified as KeyMap
import Data.Bifunctor
import Data.ByteString.Lazy as BSL (getContents, readFile)
import Data.List (intercalate)
import Data.Text (Text, replace)

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

type BuiltinCostMap = [(Text, CpuAndMemoryModel)]

-- replace underscores _ by dashes -
builtinName :: Text -> Text
builtinName = replace "_" "-"

getJSONModel :: FilePath -> IO (Maybe BuiltinCostMap)
getJSONModel jsonfile = do
  bytes <- BSL.readFile jsonfile
  case eitherDecode bytes :: Either String (KeyMap.KeyMap CpuAndMemoryModel) of
    Left err -> return Nothing
    Right m  -> return $ Just (map (first (builtinName . toText)) (KeyMap.toList m))

