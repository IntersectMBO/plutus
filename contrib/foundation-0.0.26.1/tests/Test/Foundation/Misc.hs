{-# LANGUAGE OverloadedStrings #-}
module Test.Foundation.Misc
    ( testHexadecimal
    , testUUID
    ) where

import Foundation
import Foundation.Check

import Foundation.Array.Internal (toHexadecimal)
import Test.Checks.Property.Collection (fromListP)

import qualified Foundation.UUID as UUID
import           Foundation.Parser

instance Arbitrary UUID.UUID where
    arbitrary = UUID.UUID <$> arbitrary <*> arbitrary

hex :: [Word8] -> [Word8]
hex = loop
  where
    toHex :: Int -> Word8
    toHex n
        | n < 10   = fromIntegral (n + fromEnum '0')
        | otherwise = fromIntegral (n - 10 + fromEnum 'a')
    loop []     = []
    loop (x:xs) = toHex (fromIntegral q):toHex (fromIntegral r):loop xs
      where
        (q,r) = x `divMod` 16

testHexadecimal = Group "hexadecimal"
    [ Property  "UArray(W8)" $ \l ->
        toList (toHexadecimal (fromListP (Proxy :: Proxy (UArray Word8)) l)) == hex l
    ]

testUUID = Group "UUID"
    [ Property "show" $ show UUID.nil === "00000000-0000-0000-0000-000000000000"
    , Property "show-bin" $ fmap show (UUID.fromBinary (fromList [1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16])) === Just "100f0e0d-0c0b-0a09-0807-060504030201"
    , Property "parser . show = id" $ \uuid ->
        (either (error . show) id $ parseOnly UUID.uuidParser (show uuid)) === uuid
    ]
