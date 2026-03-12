{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}

module Test.E where

import Control.DeepSeq
import Data.List
import GHC.Generics (Generic)
import PlutusCore.Flat

-- import Data.Proxy

data S3 = S_1 | S_2 Bool | S_3 Char deriving (Show, Generic, Eq, NFData)

g :: (Num a, Enum a, Show a) => a -> String
g n =
  let dt = "E" ++ show n
   in unwords
        [ "data"
        , dt
        , "="
        , intercalate " | " $ map ((\n -> dt ++ "_" ++ n) . show) [1 .. n]
        , "deriving (Show,Generic,Eq,NFData,Enum,Bounded)"
        ]

data E1 = E1 deriving (Show, Generic, Eq, NFData, Enum, Bounded)

data E2 = E2_1 | E2_2 deriving (Show, Generic, Eq, NFData, Enum, Bounded)

data E3 = E3_1 | E3_2 | E3_3 deriving (Show, Generic, Eq, NFData, Enum, Bounded)

data E4 = E4_1 | E4_2 | E4_3 | E4_4 deriving (Show, Generic, Eq, NFData, Enum, Bounded)

data E8 = E8_1 | E8_2 | E8_3 | E8_4 | E8_5 | E8_6 | E8_7 | E8_8 deriving (Show, Generic, Eq, NFData, Enum, Bounded)

data E16 = E16_1 | E16_2 | E16_3 | E16_4 | E16_5 | E16_6 | E16_7 | E16_8 | E16_9 | E16_10 | E16_11 | E16_12 | E16_13 | E16_14 | E16_15 | E16_16 deriving (Show, Generic, Eq, NFData, Enum, Bounded)

data E17 = E17_1 | E17_2 | E17_3 | E17_4 | E17_5 | E17_6 | E17_7 | E17_8 | E17_9 | E17_10 | E17_11 | E17_12 | E17_13 | E17_14 | E17_15 | E17_16 | E17_17 deriving (Show, Generic, Eq, NFData, Enum, Bounded)

data E32 = E32_1 | E32_2 | E32_3 | E32_4 | E32_5 | E32_6 | E32_7 | E32_8 | E32_9 | E32_10 | E32_11 | E32_12 | E32_13 | E32_14 | E32_15 | E32_16 | E32_17 | E32_18 | E32_19 | E32_20 | E32_21 | E32_22 | E32_23 | E32_24 | E32_25 | E32_26 | E32_27 | E32_28 | E32_29 | E32_30 | E32_31 | E32_32 deriving (Show, Generic, Eq, NFData, Enum, Bounded)
