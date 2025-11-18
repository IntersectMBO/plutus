{-# LANGUAGE ScopedTypeVariables #-}

{-
Test different ways of handlings a data type that has large values and a small encoding.

To run with limited memory: cabal run big -- +RTS  -M2g
-}

module Main where

import Data.ByteString qualified as B
import Data.List (foldl')
import ListT qualified as L
import PlutusCore.Flat (Decoded, Flat (..), flat, unflat, unflatWith)
import PlutusCore.Flat.AsBin (AsBin, unbin)
import PlutusCore.Flat.AsSize
import PlutusCore.Flat.Decoder (Get, listTDecoder)
import System.TimeIt (timeIt)

-- Big is a type that has a small encoded representation but a very large in-memory footprint.
-- It is a very large bytestring whose bytes are all set to 0
newtype Big = Big B.ByteString

newBig :: Int -> Big
newBig gigas = Big $ B.replicate (gigas * giga) 0

-- length of Big in gigas
gigas :: Big -> Int
gigas (Big b) = B.length b `div` giga

giga :: Int
giga = 1000000000

instance Show Big where show b = "Big of " ++ show (gigas b) ++ "Gbytes"

instance Flat Big where
  -- The encoded form is just the number of giga zeros (e.g. 5 for 5Giga zeros)
  size big = size (gigas big)
  encode big = encode (gigas big)

  -- The decoded form is massive
  decode = newBig <$> decode

main :: IO ()
main = tbig

tbig = do
  let numOfBigs = 5

  -- A serialised list of Big values
  let bigsFile = flat $ replicate numOfBigs $ newBig 1
  print "Encoding Time"
  timeIt $ print $ B.length bigsFile

  tstAsSize bigsFile

  tstAsBin bigsFile

  tstListT bigsFile

  tstBig bigsFile

-- If we unserialise a list of Bigs and then process them (e.g. print them out) we end up in trouble, too much memory is required.
tstBig :: B.ByteString -> IO ()
tstBig bigsFile = timeIt $ do
  print "Decode to [Big]:"
  let Right (bs :: [Big]) = unflat bigsFile
  mapM_ print bs

-- So instead we unserialise them to a list of their flat representations, to be unflatted on demand later on
tstAsBin :: B.ByteString -> IO ()
tstAsBin bigsFile = timeIt $ do
  print "Decode to [AsBin Big]:"
  let Right (bsR :: [AsBin Big]) = unflat bigsFile
  let bs = map unbin bsR
  mapM_ print bs

tstAsSize :: B.ByteString -> IO ()
tstAsSize bigsFile = timeIt $ do
  print "Decode to [AsSize Big]:"
  let Right (bs :: [AsSize Big]) = unflat bigsFile
  mapM_ print bs

-- Or: we extract one element at the time via a ListT
-- See http://hackage.haskell.org/package/list-t-1.0.4/docs/ListT.html
tstListT :: B.ByteString -> IO ()
tstListT bigsFile = timeIt $ do
  print "Decode to ListT IO Big:"
  stream :: L.ListT IO Big <- listTDecoder decode bigsFile
  L.traverse_ print stream
