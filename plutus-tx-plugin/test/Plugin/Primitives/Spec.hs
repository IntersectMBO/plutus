-- editorconfig-checker-disable-file
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# OPTIONS_GHC -fplugin Plinth.Plugin #-}
{-# OPTIONS_GHC -fplugin-opt Plinth.Plugin:context-level=3 #-}
{-# OPTIONS_GHC -fplugin-opt Plinth.Plugin:datatypes=BuiltinCasing #-}
{-# OPTIONS_GHC -fplugin-opt Plinth.Plugin:defer-errors #-}
{-# OPTIONS_GHC -fplugin-opt Plinth.Plugin:max-cse-iterations=0 #-}
{-# OPTIONS_GHC -fplugin-opt Plinth.Plugin:max-simplifier-iterations-pir=0 #-}
{-# OPTIONS_GHC -fplugin-opt Plinth.Plugin:max-simplifier-iterations-uplc=0 #-}

module Plugin.Primitives.Spec where

import Test.Tasty.Extras

import Plinth.Plugin
import PlutusCore.Test
import PlutusTx.Builtins qualified as Builtins
import PlutusTx.Code
import PlutusTx.Lift
import PlutusTx.Prelude qualified as P
import PlutusTx.Test

primitives :: TestNested
primitives =
  testNested "Primitives" . pure $
    testNestedGhc
      [ goldenPirReadable "string" string
      , goldenPirReadable "int" int
      , goldenPirReadable "int2" int2
      , goldenPirReadable "bool" bool
      , goldenPirReadable "and" andPlc
      , goldenUEval
          "andApply"
          [toUPlc andPlc, toUPlc $ plinthc True, toUPlc $ plinthc False]
      , goldenPirReadable "tuple" tuple
      , goldenPirReadable "tupleMatch" tupleMatch
      , goldenUEval "tupleConstDest" [toUPlc tupleMatch, toUPlc tuple]
      , goldenPirReadable "intCompare" intCompare
      , goldenPirReadable "intEq" intEq
      , goldenUEval "intEqApply" [toUPlc intEq, toUPlc int, toUPlc int]
      , goldenPirReadable "void" void
      , goldenPirReadable "intPlus" intPlus
      , goldenPirReadable "intDiv" intDiv
      , goldenUEval "intPlusApply" [toUPlc intPlus, toUPlc int, toUPlc int2]
      , goldenPirReadable "error" errorPlc
      , goldenPirReadable "ifThenElse" ifThenElse
      , goldenUEval "ifThenElseApply" [toUPlc ifThenElse, toUPlc int, toUPlc int2]
      , goldenPirReadable "emptyByteString" emptyByteString
      , goldenUEval
          "emptyByteStringApply"
          [getPlcNoAnn emptyByteString, snd (liftProgramDef Builtins.emptyByteString)]
      , goldenPirReadable "bytestring" bytestring
      , goldenUEval
          "bytestringApply"
          [getPlcNoAnn bytestring, snd (liftProgramDef ("hello" :: Builtins.BuiltinByteString))]
      , goldenUEval
          "sha2_256"
          [getPlcNoAnn sha2, snd (liftProgramDef ("hello" :: Builtins.BuiltinByteString))]
      , goldenUEval
          "equalsByteString"
          [ getPlcNoAnn bsEquals
          , snd (liftProgramDef ("hello" :: Builtins.BuiltinByteString))
          , snd (liftProgramDef ("hello" :: Builtins.BuiltinByteString))
          ]
      , goldenUEval
          "ltByteString"
          [ getPlcNoAnn bsLt
          , snd (liftProgramDef ("hello" :: Builtins.BuiltinByteString))
          , snd (liftProgramDef ("world" :: Builtins.BuiltinByteString))
          ]
      , goldenUEval
          "decodeUtf8"
          [getPlcNoAnn bsDecode, snd (liftProgramDef ("hello" :: Builtins.BuiltinByteString))]
      , goldenUEval
          "lengthOfByteString"
          [getPlcNoAnn bsLength, snd (liftProgramDef ("hello" :: Builtins.BuiltinByteString))]
      , goldenUEval
          "indexByteString"
          [ getPlcNoAnn bsIndex
          , snd (liftProgramDef ("hello" :: Builtins.BuiltinByteString))
          , snd (liftProgramDef (0 :: Integer))
          ]
      , goldenUEval
          "consByteString"
          [ getPlcNoAnn bsCons
          , snd (liftProgramDef (104 :: Integer))
          , snd (liftProgramDef ("ello" :: Builtins.BuiltinByteString))
          ]
      , goldenPirReadable "verify" verify
      , goldenPirReadable "trace" trace
      , goldenPirReadable "traceComplex" traceComplex
      , goldenPirReadable "stringLiteral" stringLiteral
      , goldenUEval
          "equalsString"
          [ getPlcNoAnn stringEquals
          , snd (liftProgramDef ("hello" :: Builtins.BuiltinString))
          , snd (liftProgramDef ("hello" :: Builtins.BuiltinString))
          ]
      , goldenPirReadable "encodeUtf8" stringEncode
      , goldenPirReadable "serialiseData" dataEncode
      , goldenUEval "serialiseDataApply" [toUPlc dataEncode, toUPlc constructData1]
      , goldenUEval "constructData1" [constructData1]
      , -- It's interesting to look at one of these to make sure all the specialisation is working out nicely and for
        -- debugging when it isn't
        goldenPirReadable "deconstructorData1" deconstructData1
      , -- Check that matchData works (and isn't too strict)
        goldenUEval "matchData1" [toUPlc matchData1, toUPlc constructData1]
      , goldenUEval "deconstructData1" [toUPlc deconstructData1, toUPlc constructData1]
      , goldenPirReadable "deconstructorData2" deconstructData2
      , goldenUEval "deconstructData2" [toUPlc deconstructData2, toUPlc constructData2]
      , goldenUEval "deconstructData3" [toUPlc deconstructData3, toUPlc constructData3]
      , goldenUEval "writeBits-integerToByteString" [writeBitsIntegerToByteString]
      ]

string :: CompiledCode Builtins.BuiltinString
string = plinthc "text"

int :: CompiledCode Integer
int = plinthc (1 :: Integer)

int2 :: CompiledCode Integer
int2 = plinthc (2 :: Integer)

emptyBS :: CompiledCode Builtins.BuiltinByteString
emptyBS = plinthc Builtins.emptyByteString

bool :: CompiledCode Bool
bool = plinthc True

andPlc :: CompiledCode (Bool -> Bool -> Bool)
andPlc =
  plinthc (\(x :: Bool) (y :: Bool) -> if x then (if y then True else False) else False)

tuple :: CompiledCode (Integer, Integer)
tuple = plinthc (1 :: Integer, 2 :: Integer)

tupleMatch :: CompiledCode ((Integer, Integer) -> Integer)
tupleMatch = plinthc (\(x :: (Integer, Integer)) -> let (a, _) = x in a)

intCompare :: CompiledCode (Integer -> Integer -> Bool)
intCompare = plinthc (\(x :: Integer) (y :: Integer) -> Builtins.lessThanInteger x y)

intEq :: CompiledCode (Integer -> Integer -> Bool)
intEq = plinthc (\(x :: Integer) (y :: Integer) -> Builtins.equalsInteger x y)

-- Has a Void in it
void :: CompiledCode (Integer -> Integer -> Bool)
void =
  plinthc
    ( \(x :: Integer) (y :: Integer) ->
        let a x' y' = case (x', y') of (True, True) -> True; _ -> False
         in Builtins.equalsInteger x y `a` Builtins.equalsInteger y x
    )

intPlus :: CompiledCode (Integer -> Integer -> Integer)
intPlus = plinthc (\(x :: Integer) (y :: Integer) -> Builtins.addInteger x y)

intDiv :: CompiledCode (Integer -> Integer -> Integer)
intDiv = plinthc (\(x :: Integer) (y :: Integer) -> Builtins.divideInteger x y)

errorPlc :: CompiledCode (() -> Integer)
errorPlc = plinthc (Builtins.error @Integer)

ifThenElse :: CompiledCode (Integer -> Integer -> Integer)
ifThenElse =
  plinthc
    (\(x :: Integer) (y :: Integer) -> if Builtins.equalsInteger x y then x else y)

emptyByteString :: CompiledCode (Builtins.BuiltinByteString -> Builtins.BuiltinByteString)
emptyByteString = plinthc (\(x :: Builtins.BuiltinByteString) -> x)

bytestring :: CompiledCode (Builtins.BuiltinByteString -> Builtins.BuiltinByteString)
bytestring = plinthc (\(x :: Builtins.BuiltinByteString) -> x)

sha2 :: CompiledCode (Builtins.BuiltinByteString -> Builtins.BuiltinByteString)
sha2 = plinthc (\(x :: Builtins.BuiltinByteString) -> Builtins.sha2_256 x)

bsEquals :: CompiledCode (Builtins.BuiltinByteString -> Builtins.BuiltinByteString -> Bool)
bsEquals =
  plinthc
    ( \(x :: Builtins.BuiltinByteString) (y :: Builtins.BuiltinByteString) -> Builtins.equalsByteString x y
    )

bsLength :: CompiledCode (Builtins.BuiltinByteString -> Integer)
bsLength = plinthc (\(x :: Builtins.BuiltinByteString) -> Builtins.lengthOfByteString x)

bsIndex :: CompiledCode (Builtins.BuiltinByteString -> Integer -> Integer)
bsIndex =
  plinthc
    (\(x :: Builtins.BuiltinByteString) (n :: Integer) -> Builtins.indexByteString x n)

bsCons :: CompiledCode (Integer -> Builtins.BuiltinByteString -> Builtins.BuiltinByteString)
bsCons =
  plinthc
    (\(n :: Integer) (x :: Builtins.BuiltinByteString) -> Builtins.consByteString n x)

bsLt :: CompiledCode (Builtins.BuiltinByteString -> Builtins.BuiltinByteString -> Bool)
bsLt =
  plinthc
    ( \(x :: Builtins.BuiltinByteString) (y :: Builtins.BuiltinByteString) -> Builtins.lessThanByteString x y
    )

bsDecode :: CompiledCode (Builtins.BuiltinByteString -> Builtins.BuiltinString)
bsDecode = plinthc (\(x :: Builtins.BuiltinByteString) -> Builtins.decodeUtf8 x)

verify
  :: CompiledCode
       (Builtins.BuiltinByteString -> Builtins.BuiltinByteString -> Builtins.BuiltinByteString -> Bool)
verify =
  plinthc
    ( \(x :: Builtins.BuiltinByteString) (y :: Builtins.BuiltinByteString) (z :: Builtins.BuiltinByteString) -> Builtins.verifyEd25519Signature x y z
    )

trace :: CompiledCode (Builtins.BuiltinString -> ())
trace = plinthc (\(x :: Builtins.BuiltinString) -> Builtins.trace x ())

traceComplex :: CompiledCode (Bool -> ())
traceComplex = plinthc (\(b :: Bool) -> if b then P.trace "yes" () else P.traceError "no")

stringLiteral :: CompiledCode (Builtins.BuiltinString)
stringLiteral = plinthc ("abc" :: Builtins.BuiltinString)

stringEquals :: CompiledCode (Builtins.BuiltinString -> Builtins.BuiltinString -> Bool)
stringEquals =
  plinthc
    (\(x :: Builtins.BuiltinString) (y :: Builtins.BuiltinString) -> Builtins.equalsString x y)

stringEncode :: CompiledCode (Builtins.BuiltinByteString)
stringEncode = plinthc (Builtins.encodeUtf8 "abc")

dataEncode :: CompiledCode (Builtins.BuiltinData -> Builtins.BuiltinByteString)
dataEncode = plinthc Builtins.serialiseData

constructData1 :: CompiledCode (Builtins.BuiltinData)
constructData1 = plinthc (Builtins.mkI 1)

deconstructData1 :: CompiledCode (Builtins.BuiltinData -> Integer)
deconstructData1 = plinthc (\(d :: Builtins.BuiltinData) -> Builtins.unsafeDataAsI d)

constructData2 :: CompiledCode (Builtins.BuiltinData)
constructData2 = plinthc (Builtins.mkConstr 1 [Builtins.mkI 2, Builtins.mkI 3])

deconstructData2 :: CompiledCode (Builtins.BuiltinData -> (Integer, [Integer]))
deconstructData2 =
  plinthc
    ( \(d :: Builtins.BuiltinData) -> (P.fmap . P.fmap) Builtins.unsafeDataAsI (Builtins.unsafeDataAsConstr d)
    )

constructData3 :: CompiledCode (Builtins.BuiltinData)
constructData3 = plinthc (Builtins.mkList [Builtins.mkI 2, Builtins.mkI 3])

deconstructData3 :: CompiledCode (Builtins.BuiltinData -> [Builtins.BuiltinData])
deconstructData3 = plinthc (\(d :: Builtins.BuiltinData) -> (Builtins.unsafeDataAsList d))

matchData1 :: CompiledCode (Builtins.BuiltinData -> Maybe Integer)
matchData1 =
  plinthc
    ( \(d :: Builtins.BuiltinData) -> (Builtins.matchData d (\_ _ -> Nothing) (const Nothing) (const Nothing) (Just) (const Nothing))
    )

writeBitsIntegerToByteString :: CompiledCode (P.BuiltinByteString)
writeBitsIntegerToByteString =
  plinthc
    (P.writeBits (P.writeBits (P.integerToByteString Builtins.BigEndian 6 15) [0, 5] True) [2] False)
