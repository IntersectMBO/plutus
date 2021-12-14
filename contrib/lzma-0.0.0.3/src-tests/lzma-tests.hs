{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import           Control.Applicative
import qualified Data.ByteString as BS
import qualified Data.ByteString.Lazy as BL
import           Data.List
import           Data.Monoid
import           Prelude

import           Test.Tasty
import           Test.Tasty.QuickCheck as QC
import           Test.Tasty.HUnit

import           Codec.Compression.Lzma as Lzma

main :: IO ()
main = defaultMain tests

-- this is supposed to be equivalent to 'id'
codecompress :: BL.ByteString -> BL.ByteString
codecompress = decompress . compress

newtype ZeroBS = ZeroBS BL.ByteString

instance Show ZeroBS where
    show (ZeroBS s) | BL.length s > 0 = "ZeroBS (replicate " ++ show (BL.length s) ++ " " ++ show (BL.head s) ++ ")"
                    | otherwise = "ZeroBS (empty)"

instance Arbitrary ZeroBS where
  arbitrary = do
    len <- choose (0, 1*1024*1024) -- up to 1MiB
    return $ (ZeroBS $ BL.replicate len 0)

--  shrink (ABS bs) = map ABS $ shrinks bs

randBS :: Int -> Gen BS.ByteString
randBS n = BS.pack `fmap` vectorOf n (choose (0, 255))

randBL :: Gen BL.ByteString
randBL = do
    ns <- arbitrary
    chunks <- mapM (randBS . (`mod` 10240)) ns
    return $ BL.fromChunks chunks

newtype RandBLSm = RandBLSm BL.ByteString
                 deriving Show

newtype RandBL = RandBL BL.ByteString
               deriving Show

instance Arbitrary RandBL where
    arbitrary = RandBL <$> randBL

instance Arbitrary RandBLSm where
    arbitrary = do
        n <- choose (0,1024)
        RandBLSm . BL.fromChunks . (:[]) <$> randBS n

tests :: TestTree
tests = testGroup "ByteString API" [unitTests, properties]
  where
    unitTests  = testGroup "testcases"
        [ testCase "decode-empty" $ decompress nullxz @?= BL.empty
        , testCase "encode-empty" $ codecompress BL.empty @?= BL.empty
        , testCase "encode-hello" $ codecompress "hello" @?= "hello"
        , testCase "encode-hello2" $ codecompress (singletonChunked "hello") @?= "hello"
        , testCase "decode-sample" $ decompress samplexz @?= sampleref
        , testCase "decode-sample2" $ decompress (singletonChunked samplexz) @?= sampleref
        , testCase "encode-sample" $ codecompress sampleref @?= sampleref
        , testCase "encode-empty^50" $ (iterate decompress (iterate (compressWith lowProf) "" !! 50) !! 50) @?= ""
        , testCase "encode-10MiB-zeros" $ let z = BL.replicate (10*1024*1024) 0 in codecompress z @?= z
        ]

    properties = testGroup "properties"
        [ QC.testProperty "decompress . compress === id (zeros)" $
          \(ZeroBS bs) -> codecompress bs == bs

        , QC.testProperty "decompress . compress === id (chunked)" $
          \(RandBL bs) -> codecompress bs == bs

        , QC.testProperty "decompress . (compress a <> compress b) === a <> b" $
          \(RandBLSm a) (RandBLSm b) -> decompress (compress a `mappend` compress b) == a `mappend` b
        ]

    lowProf = defaultCompressParams { compressLevel = CompressionLevel0 }

nullxz :: BL.ByteString
nullxz = BL.pack [253,55,122,88,90,0,0,4,230,214,180,70,0,0,0,0,28,223,68,33,31,182,243,125,1,0,0,0,0,4,89,90]

samplexz :: BL.ByteString
samplexz = BL.pack [253,55,122,88,90,0,0,4,230,214,180,70,2,0,33,1,16,0,0,0,168,112,142,134,224,1,149,0,44,93,0,42,26,9,39,100,25,234,181,131,189,58,102,36,15,228,64,252,88,41,53,203,78,255,4,93,168,153,174,39,186,76,120,56,49,148,191,144,96,136,20,247,240,0,0,0,157,204,158,16,53,174,37,20,0,1,72,150,3,0,0,0,130,33,173,108,177,196,103,251,2,0,0,0,0,4,89,90]

singletonChunked :: BL.ByteString -> BL.ByteString
singletonChunked = BL.fromChunks . map BS.singleton . BL.unpack

sampleref :: BL.ByteString
sampleref = BL.concat (intersperse " " $ replicate 11 "This sentence occurs multiple times.")
