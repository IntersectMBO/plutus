{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE NoImplicitPrelude   #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies        #-}
{-# LANGUAGE OverloadedStrings   #-}
module Test.Foundation.String
    ( testStringRefs
    ) where

-- import Control.Monad (replicateM)

import Foundation
import Foundation.Check
import Foundation.String
import Foundation.Primitive (AsciiString)

import Test.Data.List
import Test.Checks.Property.Collection
--import Test.Foundation.Encoding

testStringRefs :: Test
testStringRefs = Group "String"
    [ Group "UTF8" $
        [  collectionProperties "String" (Proxy :: Proxy String) arbitrary ]
        <> testStringCases
        {-
        <> [ testGroup "Encoding Sample0" (testEncodings sample0)
           , testGroup "Encoding Sample1" (testEncodings sample1)
           , testGroup "Encoding Sample2" (testEncodings sample2)
           ]
           -}
    , Group "ASCII" $
        [  collectionProperties "AsciiString" (Proxy :: Proxy AsciiString) arbitrary ]
        -- <> testAsciiStringCases
    ]

testStringCases :: [Test]
testStringCases =
    [ Group "Validation"
        [ Property "fromBytes . toBytes == valid" $ \l ->
            let s = fromList l
             in (fromBytes UTF8 $ toBytes UTF8 s) === (s, Nothing, mempty)
        , Property "Streaming" $ \(l, randomInts) ->
            let wholeS  = fromList l
                wholeBA = toBytes UTF8 wholeS
                reconstruct (prevBa, errs, acc) ba =
                    let ba' = prevBa `mappend` ba
                        (s, merr, nextBa) = fromBytes UTF8 ba'
                     in (nextBa, merr : errs, s : acc)

                (remainingBa, allErrs, chunkS) = foldl' reconstruct (mempty, [], []) $ chunks randomInts wholeBA
             in (catMaybes allErrs === []) `propertyAnd` (remainingBa === mempty) `propertyAnd` (mconcat (reverse chunkS) === wholeS)
        ]
    , Group "ModifiedUTF8"
        [ propertyModifiedUTF8 "The foundation Serie" "基地系列" "基地系列"
        , propertyModifiedUTF8 "has null bytes" "let's\0 do \0 it" "let's\0 do \0 it"
        , propertyModifiedUTF8 "Vincent's special" "abc\0안, 蠀\0, ☃" "abc\0안, 蠀\0, ☃"
        , propertyModifiedUTF8 "Long string"
              "this is only a simple string but quite longer than the 64 bytes used in the modified UTF8 parser"
              "this is only a simple string but quite longer than the 64 bytes used in the modified UTF8 parser"
        ]
    , Group "CaseMapping" 
         [ Property "upper . upper == upper" $ \l ->
             let s = fromList l
              in upper (upper s) === upper s
         , CheckPlan "a should capitalize to A" $ validate "a" $ upper "a" == "A"
         , CheckPlan "b should capitalize to B" $ validate "b" $ upper "b" == "B"
         , CheckPlan "B should not capitalize" $ validate "B" $ upper "B" == "B"
         , CheckPlan "é should capitalize to É" $ validate "é" $ upper "é" == "É"
         , CheckPlan "ß should capitalize to SS" $ validate "ß" $ upper "ß" == "SS"
         , CheckPlan "ﬄ should capitalize to FFL" $ validate "ﬄ" $ upper "ﬄﬄﬄﬄﬄﬄﬄﬄﬄﬄ" == "FFLFFLFFLFFLFFLFFLFFLFFLFFLFFL"
         , CheckPlan "0a should capitalize to 0A" $ validate "0a" $ upper "\0a" == "\0A"
         , CheckPlan "0a should capitalize to 0A" $ validate "0a" $ upper "a\0a" == "A\0A"
         , CheckPlan "0a should capitalize to 0A" $ validate "0a" $ upper "\0\0" == "\0\0"
         , CheckPlan "00 should not capitalize" $ validate "00" $ upper "00" == "00"
        ]
    {-
    , testGroup "replace" [
          testCase "indices '' 'bb' should raise an error" $ do
            res <- try (evaluate $ indices "" "bb")
            case res of
              (Left (_ :: SomeException)) -> return ()
              Right _ -> fail "Expecting an error to be thrown, but it did not."
        , testCase "indices 'aa' 'bb' == []" $ do
            indices "aa" "bb" @?= []
        , testCase "indices 'aa' 'aabbccabbccEEaaaaabb' is correct" $ do
            indices "aa" "aabbccabbccEEaaaaabb" @?= [Offset 0,Offset 13,Offset 15]
        , testCase "indices 'aa' 'aaccaadd' is correct" $ do
            indices "aa" "aaccaadd" @?= [Offset 0,Offset 4]
        , testCase "replace '' 'bb' 'foo' raises an error" $ do
            (res :: Either SomeException String) <- try (evaluate $ replace "" "bb" "foo")
            assertBool "Expecting an error to be thrown, but it did not." (isLeft res)
        , testCase "replace 'aa' 'bb' '' == ''" $ do
            replace "aa" "bb" "" @?= ""
        , testCase "replace 'aa' '' 'aabbcc' == 'aabbcc'" $ do
            replace "aa" "" "aabbcc" @?= "bbcc"
        , testCase "replace 'aa' 'bb' 'aa' == 'bb'" $ do
            replace "aa" "bb" "aa" @?= "bb"
        , testCase "replace 'aa' 'bb' 'aabb' == 'bbbb'" $ do
            replace "aa" "bb" "aabb" @?= "bbbb"
        , testCase "replace 'aa' 'bb' 'aaccaadd' == 'bbccbbdd'" $ do
            replace "aa" "bb" "aaccaadd" @?= "bbccbbdd"
        , testCase "replace 'aa' 'LongLong' 'aaccaadd' == 'LongLongccLongLongdd'" $ do
            replace "aa" "LongLong" "aaccaadd" @?= "LongLongccLongLongdd"
        , testCase "replace 'aa' 'bb' 'aabbccabbccEEaaaaabb' == 'bbbbccabbccEEbbbbabb'" $ do
            replace "aa" "bb" "aabbccabbccEEaaaaabb" @?= "bbbbccabbccEEbbbbabb"
        , testCase "replace 'å' 'ä' 'ååññ' == 'ääññ'" $ do
            replace "å" "ä" "ååññ" @?= "ääññ"
                          ]
    , testGroup "Cases"
        [ testGroup "Invalid-UTF8"
            [ testCase "ff" $ expectFromBytesErr UTF8 ("", Just InvalidHeader, 0) (fromList [0xff])
            , testCase "80" $ expectFromBytesErr UTF8 ("", Just InvalidHeader, 0) (fromList [0x80])
            , testCase "E2 82 0C" $ expectFromBytesErr UTF8 ("", Just InvalidContinuation, 0) (fromList [0xE2,0x82,0x0c])
            , testCase "30 31 E2 82 0C" $ expectFromBytesErr UTF8 ("01", Just InvalidContinuation, 2) (fromList [0x30,0x31,0xE2,0x82,0x0c])
            ]
        ]
    , testGroup "Lines"
        [ testCase "Hello<LF>Foundation" $
            (breakLine "Hello\nFoundation" @?= Right ("Hello", "Foundation"))
        , testCase "Hello<CRLF>Foundation" $
            (breakLine "Hello\r\nFoundation" @?= Right ("Hello", "Foundation"))
        , testCase "Hello<LF>Foundation" $
            (breakLine (drop 5 "Hello\nFoundation\nSomething") @?= Right ("", "Foundation\nSomething"))
        , testCase "Hello<CR>" $
            (breakLine "Hello\r" @?= Left True)
        , testCase "CR" $
            (breakLine "\r" @?= Left True)
        , testCase "LF" $
            (breakLine "\n" @?= Right ("", ""))
        , testCase "empty" $
            (breakLine "" @?= Left False)
        ]
        -}
    ]

{-
testAsciiStringCases :: [Test]
testAsciiStringCases =
    [ Group "Validation-ASCII7"
        [ Property "fromBytes . toBytes == valid" $ \l ->
             let s = fromList . fromLStringASCII $ l
             in (fromBytes ASCII7 $ toBytes ASCII7 s) === (s, Nothing, mempty)
        , Property "Streaming" $ \(l, randomInts) ->
            let wholeS  = fromList . fromLStringASCII $ l
                wholeBA = toBytes ASCII7 wholeS
                reconstruct (prevBa, errs, acc) ba =
                    let ba' = prevBa `mappend` ba
                        (s, merr, nextBa) = fromBytes ASCII7 ba'
                     in (nextBa, merr : errs, s : acc)

                (remainingBa, allErrs, chunkS) = foldl' reconstruct (mempty, [], []) $ chunks randomInts wholeBA
             in (catMaybes allErrs === []) .&&. (remainingBa === mempty) .&&. (mconcat (reverse chunkS) === wholeS)
        ]
    , Group "Cases"
        [ Group "Invalid-ASCII7"
            [ testCase "ff" $ expectFromBytesErr ASCII7 ("", Just BuildingFailure, 0) (fromList [0xff])
            ]
        ]
    ]

expectFromBytesErr :: Encoding -> ([Char], Maybe ValidationFailure, CountOf Word8) -> UArray Word8 -> IO ()
expectFromBytesErr enc (expectedString,expectedErr,positionErr) ba = do
    let x = fromBytes enc ba
        (s', merr, ba') = x
    assertEqual "error" expectedErr merr
    assertEqual "remaining" (drop positionErr ba) ba'
    assertEqual "string" expectedString (toList s')
-}

propertyModifiedUTF8 :: String -> [Char] -> String -> Test
propertyModifiedUTF8 name chars str = Property name $ chars === toList str

chunks :: Sequential c => RandomList -> c -> [c]
chunks (RandomList randomInts) = loop (randomInts <> [1..])
  where
    loop rx c
        | null c  = []
        | otherwise =
            case rx of
                r:rs ->
                    let (c1,c2) = splitAt (CountOf r) c
                     in c1 : loop rs c2
                [] ->
                    loop randomInts c
