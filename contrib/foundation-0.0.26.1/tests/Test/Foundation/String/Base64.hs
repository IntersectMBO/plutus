{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE NoImplicitPrelude   #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies        #-}
module Test.Foundation.String.Base64
    ( testBase64Refs
    ) where

import Control.Monad
import Foundation
import Foundation.Numerical
import Foundation.String
import Foundation.Check

testBase64Refs :: Test
testBase64Refs = Group "String"
    [ Group "Base64" testBase64Cases
    ]

testBase64Cases :: [Test]
testBase64Cases =
    [ Group "toBase64"
        [ Property "length with padding" $ \l ->
            let s = fromList l
                b = toBytes UTF8 s
                blen = length b
             in (length . toBytes UTF8 . toBase64 $ s) === outputLengthBase64 True blen
        , Property "valid chars" $ \l ->
            let s = fromList l
                s64 = toBase64 s
                b64 = toBytes UTF8 s64
            in all ((||) <$> isPlainBase64Char <*> isPadding) b64 === True
        , Property "test string: 'pleasure.'" $ do
            let s = fromList "pleasure."
            toBase64 s === fromList "cGxlYXN1cmUu"
        , Property "test string: 'leasure.'" $ do
            let s = fromList "leasure."
            toBase64 s === fromList "bGVhc3VyZS4="
        , Property "test string: 'easure.'" $ do
            let s = fromList "easure."
            toBase64 s === fromList "ZWFzdXJlLg=="
        , Property "test string: 'asure.'" $ do
            let s = fromList "asure."
            toBase64 s === fromList "YXN1cmUu"
        , Property "test string: 'sure.'" $ do
            let s = fromList "sure."
            toBase64 s === fromList "c3VyZS4="
        ]
    , Group "toBase64OpenBSD"
        [ Property "length without padding" $ \l ->
            let s = fromList l
                b = toBytes UTF8 s
                blen = length b
            in (length . toBytes UTF8 . toBase64OpenBSD $ s) === outputLengthBase64 False blen
        , Property "valid chars" $ \l ->
            let s = fromList l
                s64 = toBase64OpenBSD s
                b64 = toBytes UTF8 s64
            in all isBase64OpenBSDChar b64 === True
        ]
    , Group "toBase64URL"
        [ Property "length with padding" $ \l ->
            let s = fromList l
                b = toBytes UTF8 s
                blen = length b
            in (length . toBytes UTF8 . toBase64URL True $ s) === outputLengthBase64 True blen,
          Property "length without padding" $ \l ->
            let s = fromList l
                b = toBytes UTF8 s
                blen = length b
            in (length . toBytes UTF8 . toBase64URL False $ s) === outputLengthBase64 False blen
        , Property "valid chars (with padding)" $ \l ->
            let s = fromList l
                s64 = toBase64URL True s
                b64 = toBytes UTF8 s64
            in all ((||) <$> isBase64URLChar <*> isPadding) b64 === True
        , Property "valid chars (without padding)" $ \l ->
            let s = fromList l
                s64 = toBase64URL False s
                b64 = toBytes UTF8 s64
            in all isBase64URLChar b64 === True
        , Property "test string: 'pleasure.'" $ do
            let s = fromList "pleasure."
            toBase64URL False s === fromList "cGxlYXN1cmUu"
        , Property "test string: 'leasure.'" $ do
            let s = fromList "leasure."
            toBase64URL False s === fromList "bGVhc3VyZS4"
        , Property "test string: '<empty>'" $ do
            let s = fromList ""
            toBase64URL False s === fromList ""
        , Property "test string: '\\DC4\\251\\156\\ETX\\217~'" $ do
            -- the byte list represents "\DC4\251\156\ETX\217~"
            let s = fromBytesUnsafe . fromList $ [0x14, 0xfb, 0x9c, 0x03, 0xd9, 0x7e]
            toBase64URL False s === fromList "FPucA9l-"
        , Property "test string: '\\DC4\\251\\156\\ETX\\217\\DEL'" $ do
            -- the byte list represents "\DC4\251\156\ETX\217\DEL"
            let s = fromBytesUnsafe . fromList $ [0x14, 0xfb, 0x9c, 0x03, 0xd9, 0x7f]
            toBase64URL False s === fromList "FPucA9l_"
        ]
    ]

outputLengthBase64 :: Bool -> CountOf Word8 -> CountOf Word8
outputLengthBase64 padding (CountOf inputLenInt) = outputLength
  where
    outputLength = if padding then CountOf lenWithPadding else CountOf (lenWithPadding - numPadChars)

    lenWithPadding :: Int
    lenWithPadding = 4 * roundUp (fromIntegral inputLenInt / 3.0 :: Double)

    numPadChars :: Int
    numPadChars = case inputLenInt `mod` 3 of
        1 -> 2
        2 -> 1
        _ -> 0

isPlainBase64Char :: Word8 -> Bool
isPlainBase64Char w = isAlphaDigit w || isPlus w || isSlash w

isBase64URLChar :: Word8 -> Bool
isBase64URLChar w = isAlphaDigit w || isDash w || isUnderscore w

isBase64OpenBSDChar :: Word8 -> Bool
isBase64OpenBSDChar w = isPeriod w || isSlash w || isAlphaDigit w

isPadding :: Word8 -> Bool
isPadding w = w == 61

isAlphaDigit :: Word8 -> Bool
isAlphaDigit w = isAlpha w || isDigit w

isAlpha :: Word8 -> Bool
isAlpha w = isUpperAlpha w || isLowerAlpha w

isUpperAlpha :: Word8 -> Bool
isUpperAlpha w = w - 65 <= 25

isLowerAlpha :: Word8 -> Bool
isLowerAlpha w = w - 97 <= 25

isDigit :: Word8 -> Bool
isDigit w = w - 48 <= 9

isPlus :: Word8 -> Bool
isPlus w = w == 43

isSlash :: Word8 -> Bool
isSlash w = w == 47

isDash :: Word8 -> Bool
isDash w = w == 45

isUnderscore :: Word8 -> Bool
isUnderscore w = w == 95

isPeriod :: Word8 -> Bool
isPeriod w = w == 46
