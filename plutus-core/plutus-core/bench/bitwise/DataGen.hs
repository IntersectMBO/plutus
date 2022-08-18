{-# LANGUAGE KindSignatures      #-}
{-# LANGUAGE ScopedTypeVariables #-}

module DataGen (
  mkUnaryArg,
  mkHomogenousArg,
  mkBinaryArgs,
  mkZeroesOne,
  sizes,
  noCleanup,
  ) where

import Control.Monad (replicateM)
import Data.ByteString (ByteString)
import Data.ByteString qualified as BS
import Data.Kind (Type)
import Data.Word (Word8)
import GHC.Exts (fromListN)
import System.Random.Stateful (mkStdGen, randomM, runStateGen_)

-- Generate a ByteString of a given length
mkUnaryArg :: Int -> IO ByteString
mkUnaryArg len = pure . runStateGen_ (mkStdGen 42) $ \gen ->
  fromListN len <$> replicateM len (randomM gen)

-- Generate a ByteString of a given length full of the given byte
mkHomogenousArg :: Int -> Word8 -> IO ByteString
mkHomogenousArg len = pure . BS.replicate len

-- Generates n - 1 zeroes, followed by a one byte
mkZeroesOne :: Int -> IO ByteString
mkZeroesOne len = pure $ BS.snoc (BS.replicate (len - 1) 0x00) 0x01

-- Generate two ByteStrings, both of a given length
mkBinaryArgs :: Int -> IO (ByteString, ByteString)
mkBinaryArgs len = pure . runStateGen_ (mkStdGen 42) $ \gen ->
  (,) <$> (fromListN len <$> replicateM len (randomM gen)) <*>
          (fromListN len <$> replicateM len (randomM gen))

-- We work in IO only to avoid interference, so thus, a cleanup isn't needed for
-- withResource. This function is designed to indicate that fact.
noCleanup :: forall (a :: Type) . a -> IO ()
noCleanup = const (pure ())

-- Basic set of sizes (in bytes)
sizes :: [Int]
sizes = [((2 :: Int) ^ (i :: Int) - 1) | i <- [1 .. 15]]
