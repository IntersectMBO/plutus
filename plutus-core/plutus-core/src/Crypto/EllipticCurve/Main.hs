-- editorconfig-checker-disable-file
module Main where

-- FIXME: if the size information was exported from Crypto.EllipticCurve.BLS12
-- then we'd be able to use it directly where required.

import Crypto.EllipticCurve.BLS12_381.Internal
import Data.Proxy
import Text.Printf

sizeInfo :: Integer -> String
sizeInfo n = printf "%3d bytes  / %3d words" n (n `div` 8)

main :: IO ()
main = do
  printf "G1 memory size:     %s\n" $ sizeInfo ((sizeP (Proxy :: Proxy Curve1)) :: Integer)
  printf "G1 compressed size: %s\n" $ sizeInfo ((compressedSizeP (Proxy :: Proxy Curve1)) :: Integer)
  printf "G1 serialised size: %s\n" $ sizeInfo ((serializedSizeP (Proxy :: Proxy Curve1)) :: Integer)
  printf "G1 affine size:     %s\n" $ sizeInfo ((sizeAffine (Proxy :: Proxy Curve1)) :: Integer)
  printf "\n"
  printf "G2 memory size:     %s\n" $ sizeInfo ((sizeP (Proxy :: Proxy Curve2)) :: Integer)
  printf "G2 compressed size: %s\n" $ sizeInfo ((compressedSizeP (Proxy :: Proxy Curve2)) :: Integer)
  printf "G2 serialised size: %s\n" $ sizeInfo ((serializedSizeP (Proxy :: Proxy Curve2)) :: Integer)
  printf "G2 affine size:     %s\n" $ sizeInfo ((sizeAffine (Proxy :: Proxy Curve2)) :: Integer)
  printf "\n"
  printf "GT memory size:     %s\n" $ sizeInfo (sizePT:: Integer)
