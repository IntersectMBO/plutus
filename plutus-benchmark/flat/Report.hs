{-# LANGUAGE DeriveGeneric     #-}
{-# LANGUAGE OverloadedStrings #-}

{-|
Collecting data about the size of serialied terms is not exactly a proper benchmark.
We need to process the serialized results to collect the size of the term serialized
usign different contracts and different codecs.
-}
module Report ( Size(..)
              , Ratio(..)
              , Measures
              , measureSize
              , withRatio
              , showContractMeasures
              , showCodecSizes
              ) where

import           Control.Lens
import qualified Data.ByteString        as BS
import           Data.Function          (on)
import           Data.List              (sort)
import           Data.Map               (Map)
import qualified Data.Map               as Map
import           Data.Text              (Text, pack, unpack)
import           GHC.Generics
import           Text.PrettyPrint.Boxes

import           Prelude                as P

-- | Data collected for the size of contracts
data Size = Size
  { szContract :: Text -- ^ Contract name
  , szCodec    :: Text -- ^ Codec used for serialization
  , szBytes    :: Integer -- ^ Size of serialized codec
  } deriving (Eq, Show, Generic)

-- | Measures
type Measures = Map Text [Size]

-- | Order by contract name and serialized contract size.
instance Ord Size where
  compare = (compare `on` szContract) P.<> (compare `on` szBytes)

-- | Transform the Map we get when we serialized the data (before running the
--   benchmarks) to a Map of Sizes indexed by the contract that was serialized
measureSize ::
     Map (Text, Text) BS.ByteString
  -> Map Text [Size]
measureSize =
  Map.map sort .
  Map.foldlWithKey go Map.empty
  where
    go :: Map Text [Size] -> (Text, Text) -> BS.ByteString -> Map Text [Size]
    go ms (contractName, codecName) contract =
      let sizeMs = Size { szContract = contractName
                        , szCodec    = codecName
                        , szBytes    = fromIntegral $ BS.length contract
                        }
      in ms & at contractName <>~ Just [sizeMs]

-- | For each measurement we add a ratio that shows how codecs compare for the same
-- contract.
data Ratio = Ratio
  { ofMinimum :: Float
  , ofMaximum :: Float
  }

{- | Compute minimum and maximum ratios over a list of measurements.
     Note that I assume sizes are ordered -}
withRatio :: Map Text [Size]
          -> Map Text [(Size, Ratio)]
withRatio =
  Map.map computeRatio
  where
    computeRatio :: [Size] -> [(Size, Ratio)]
    computeRatio sizes =
      let minimumSize = fromInteger $ szBytes $ head sizes
          maximumSize = fromInteger $ szBytes $ last sizes
      in P.map (addRatio minimumSize maximumSize) sizes
    addRatio :: Float -> Float -> Size -> (Size, Ratio)
    addRatio min' max' size =
      (size, Ratio { ofMaximum = fromInteger (szBytes size) / max'
                   , ofMinimum = fromInteger (szBytes size) / min' })

-- | Pretty print serialized measures.
showContractMeasures :: Map Text [(Size, Ratio)]
              -> Text
showContractMeasures =
  Map.foldMapWithKey go
  where
    go :: Text -> [(Size, Ratio)] -> Text
    go contractName sizes =
      "** Contract: " P.<> contractName P.<> " **\n" P.<>
      (pack . render $ showCodecSizes sizes) P.<> "\n"

-- | Pretty print (as a table) information about sizes, codecs and ratios.
showCodecSizes :: [(Size, Ratio)] -> Box
showCodecSizes sizes =
  hsep 3 left $
    [ vcat top $ text "Codec" : map (text . unpack . szCodec . fst) sizes
    , vcat top $ text "Size"  : map (text . show . szBytes . fst) sizes
    , vcat top $ text "Of minimum" : map (text . show . ofMinimum . snd) sizes
    , vcat top $ text "Of maximum" : map (text . show . ofMaximum . snd) sizes
    ]
