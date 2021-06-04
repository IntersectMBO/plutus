{-# LANGUAGE BangPatterns               #-}
{-# LANGUAGE DataKinds                  #-}
{-# LANGUAGE DeriveGeneric              #-}
{-# LANGUAGE GADTs                      #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MagicHash                  #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE StandaloneDeriving         #-}
{-# LANGUAGE TypeApplications           #-}

{-# OPTIONS_GHC -fno-warn-orphans #-}

import           Test.Tasty.Bench        (bench, bgroup, defaultMain, env, nf, nfIO)

import           Control.Monad.Primitive
import           Data.Foldable           (for_)
import           Data.Functor.Const
import           Data.Monoid
import           Data.Primitive
import           Data.Word
import           Data.Word64Array.Word8

main :: IO ()
main = do
  let someArray = toWordArray (maxBound `div` 2)
      {-# NOINLINE someArray #-}
      mkPrimArray = do
          arr <- newPrimArray 8
          setPrimArray arr 0 8 (0 :: Word8)
          pure arr
      {-# NOINLINE mkPrimArray #-}
      overIndexPA :: (Prim a, PrimMonad m) => Int -> (a -> a) -> MutablePrimArray (PrimState m) a -> m ()
      overIndexPA i f arr = do
          v <- readPrimArray arr i
          writePrimArray arr i (f v)
      iforPrimArray :: (Prim a, PrimMonad m) => MutablePrimArray (PrimState m) a -> (Int -> a -> m ()) -> m ()
      iforPrimArray arr f = for_ [0..sizeofMutablePrimArray arr] $ \i -> do
          v <- readPrimArray arr i
          f i v

  defaultMain
    [
      bgroup "word-array"
        [ bench "overIndex" $ nf (overIndex 0 (+1)) someArray
        , bench "ifor" $ nf (flip iforWordArray (\i w -> Const $ Sum i)) (toWordArray maxBound)
        ]
      , bgroup "prim-array"
        [ env mkPrimArray $ \arr -> bench "overIndex" $ nfIO (overIndexPA 0 (+1) arr)
        , env mkPrimArray $ \arr -> bench "ifor" $ nfIO (flip iforPrimArray (\i w -> pure ()) arr)
        ]
    ]
