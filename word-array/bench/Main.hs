-- editorconfig-checker-disable-file
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE ScopedTypeVariables #-}

{-# OPTIONS_GHC -fno-warn-orphans #-}

import Test.Tasty.Bench (bench, bgroup, defaultMain, env, nf, nfIO)

import Control.Monad.Primitive
import Data.Foldable (for_)
import Data.Functor.Const
import Data.Monoid
import Data.Primitive
import Data.Word
import Data.Word128Array.Word8 qualified as WA128
import Data.Word64Array.Word8 qualified as WA64

main :: IO ()
main = do
  let someArray64 = WA64.toWordArray (maxBound `div` 2)
      {-# NOINLINE someArray64 #-}
      someArray128 = WA128.toWordArray (maxBound `div` 2)
      {-# NOINLINE someArray128 #-}
      mkPrimArray64 = do
          arr <- newPrimArray 8
          setPrimArray arr 0 8 (0 :: Word8)
          pure arr
      {-# NOINLINE mkPrimArray64 #-}
      mkPrimArray128 = do
          arr <- newPrimArray 16
          setPrimArray arr 0 16 (0 :: Word8)
          pure arr
      {-# NOINLINE mkPrimArray128 #-}
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
      bgroup "word-array (64)"
        [ bench "overIndex" $ nf (WA64.overIndex 0 (+1)) someArray64
        , bench "ifor" $ nf (flip WA64.iforWordArray (\i _ -> Const $ Sum i)) (WA64.toWordArray maxBound)
        ]
      , bgroup "word-array (128)"
        [ bench "overIndex" $ nf (WA128.overIndex 0 (+1)) someArray128
        , bench "ifor" $ nf (flip WA128.iforWordArray (\i _ -> Const $ Sum i)) (WA128.toWordArray maxBound)
        ]
      , bgroup "prim-array (64)"
        [ env mkPrimArray64 $ \arr -> bench "overIndex" $ nfIO (overIndexPA 0 (+1) arr)
        , env mkPrimArray64 $ \arr -> bench "ifor" $ nfIO (flip iforPrimArray (\_ _ -> pure ()) arr)
        ]
      , bgroup "prim-array (128)"
        [ env mkPrimArray128 $ \arr -> bench "overIndex" $ nfIO (overIndexPA 0 (+1) arr)
        , env mkPrimArray128 $ \arr -> bench "ifor" $ nfIO (flip iforPrimArray (\_ _ -> pure ()) arr)
        ]
    ]
