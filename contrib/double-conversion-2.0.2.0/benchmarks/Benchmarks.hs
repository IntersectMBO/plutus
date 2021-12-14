{-# LANGUAGE ForeignFunctionInterface, OverloadedStrings #-}

import Criterion.Main
import qualified Data.Double.Conversion.ByteString as B
import qualified Data.Double.Conversion.Text as T
import Foreign.C.Types (CInt(CInt), CDouble(CDouble))
import qualified Data.Text as T
import qualified Text.Show.ByteString as BS

main = defaultMain [
         bgroup "haskell" [
           bench "show" $ nf show (pi::Double)
         , bench "bytestring-show" $ whnf BS.show (pi::Double)
         , bgroup "text" [
             bench "toShortest" $ whnf T.toShortest pi
           , bench "toExponential" $ whnf (T.toExponential 3) pi
           , bench "toPrecision" $ whnf (T.toExponential 8) pi
           , bench "toFixed" $ whnf (T.toFixed 8) pi
           ]
         , bgroup "bytestring" [
             bench "toShortest" $ whnf B.toShortest pi
           , bench "toExponential" $ whnf (B.toExponential 3) pi
           , bench "toPrecision" $ whnf (B.toExponential 8) pi
           , bench "toFixed" $ whnf (B.toFixed 8) pi
           ]
         ]
       , bgroup "sprintf" [
           bench "exact" $ whnf sprintf_exact pi
         , bench "exponential" $ whnf (sprintf_exponential 3) pi
         , bench "fixed" $ whnf (sprintf_fixed 8) pi
         , bench "generic" $ whnf (sprintf_generic 6) pi
         , bench "generic_default" $ whnf sprintf_generic_default pi
         ]
       ]

foreign import ccall unsafe sprintf_exact :: CDouble -> ()
foreign import ccall unsafe sprintf_exponential :: CInt -> CDouble -> ()
foreign import ccall unsafe sprintf_fixed :: CInt -> CDouble -> ()
foreign import ccall unsafe sprintf_generic :: CInt -> CDouble -> ()
foreign import ccall unsafe sprintf_generic_default :: CDouble -> ()
