-- editorconfig-checker-disable-file
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}
{-# OPTIONS_GHC -fplugin PlutusTx.Plugin #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:defer-errors #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:context-level=3 #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:max-simplifier-iterations-pir=0 #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:max-simplifier-iterations-uplc=0 #-}

module Plugin.Primitives.Spec where

import Test.Tasty.Extras

import PlutusCore.Test
import PlutusTx.Builtins qualified as Builtins
import PlutusTx.Code
import PlutusTx.Lift
import PlutusTx.Plugin
import PlutusTx.Prelude qualified as P
import PlutusTx.Test

import Data.Proxy

primitives :: TestNested
primitives = testNestedGhc "Primitives" [
    goldenPir "string" string
  , goldenPir "int" int
  , goldenPir "int2" int2
  , goldenPir "bool" bool
  , goldenPir "and" andPlc
  , goldenUEval "andApply" [ toUPlc andPlc, toUPlc $ plc (Proxy @"T") True, toUPlc $ plc (Proxy @"F") False ]
  , goldenPir "tuple" tuple
  , goldenPir "tupleMatch" tupleMatch
  , goldenUEval "tupleConstDest" [ toUPlc tupleMatch, toUPlc tuple ]
  , goldenPir "intCompare" intCompare
  , goldenPir "intEq" intEq
  , goldenUEval "intEqApply" [ toUPlc intEq, toUPlc int, toUPlc int ]
  , goldenPir "void" void
  , goldenPir "intPlus" intPlus
  , goldenPir "intDiv" intDiv
  , goldenUEval "intPlusApply" [ toUPlc intPlus, toUPlc int, toUPlc int2 ]
  , goldenPir "error" errorPlc
  , goldenPir "ifThenElse" ifThenElse
  , goldenUEval "ifThenElseApply" [ toUPlc ifThenElse, toUPlc int, toUPlc int2 ]
  , goldenPir "emptyByteString" emptyByteString
  , goldenUEval "emptyByteStringApply" [ getPlcNoAnn emptyByteString, snd (liftProgramDef Builtins.emptyByteString) ]
  , goldenPir "bytestring" bytestring
  , goldenUEval "bytestringApply" [ getPlcNoAnn bytestring, snd (liftProgramDef ("hello" ::Builtins.BuiltinByteString)) ]
  , goldenUEval "sha2_256" [ getPlcNoAnn sha2, snd (liftProgramDef ("hello" :: Builtins.BuiltinByteString))]
  , goldenUEval "equalsByteString" [ getPlcNoAnn bsEquals, snd (liftProgramDef ("hello" :: Builtins.BuiltinByteString)), snd (liftProgramDef ("hello" :: Builtins.BuiltinByteString))]
  , goldenUEval "ltByteString" [ getPlcNoAnn bsLt, snd (liftProgramDef ("hello" :: Builtins.BuiltinByteString)), snd (liftProgramDef ("world" :: Builtins.BuiltinByteString))]
  , goldenUEval "decodeUtf8" [ getPlcNoAnn bsDecode, snd (liftProgramDef ("hello" :: Builtins.BuiltinByteString))]
  , goldenUEval "lengthOfByteString" [ getPlcNoAnn bsLength, snd (liftProgramDef ("hello" :: Builtins.BuiltinByteString))]
  , goldenUEval "indexByteString" [ getPlcNoAnn bsIndex, snd (liftProgramDef ("hello" :: Builtins.BuiltinByteString)), snd (liftProgramDef (0 :: Integer))]
  , goldenUEval "consByteString" [ getPlcNoAnn bsCons, snd (liftProgramDef (104 :: Integer)), snd (liftProgramDef ("ello" :: Builtins.BuiltinByteString))]
  , goldenPir "verify" verify
  , goldenPir "trace" trace
  , goldenPir "traceComplex" traceComplex
  , goldenPir "stringLiteral" stringLiteral
  , goldenUEval "equalsString" [ getPlcNoAnn stringEquals, snd (liftProgramDef ("hello" :: Builtins.BuiltinString)), snd (liftProgramDef ("hello" :: Builtins.BuiltinString))]
  , goldenPir "encodeUtf8" stringEncode
  , goldenPir "serialiseData" dataEncode
  , goldenUEval "serialiseDataApply" [ toUPlc dataEncode, toUPlc constructData1 ]
  , goldenUEval "constructData1" [ constructData1 ]
  -- It's interesting to look at one of these to make sure all the specialisation is working out nicely and for
  -- debugging when it isn't
  , goldenPir "deconstructorData1" deconstructData1
  -- Check that matchData works (and isn't too strict)
  , goldenUEval "matchData1" [ toUPlc matchData1, toUPlc constructData1 ]
  , goldenUEval "deconstructData1" [ toUPlc deconstructData1, toUPlc constructData1 ]
  , goldenPir "deconstructorData2" deconstructData2
  , goldenUEval "deconstructData2" [ toUPlc deconstructData2, toUPlc constructData2 ]
  , goldenUEval "deconstructData3" [ toUPlc deconstructData3, toUPlc constructData3 ]
  ]

string :: CompiledCode Builtins.BuiltinString
string = plc (Proxy @"text") "text"

int :: CompiledCode Integer
int = plc (Proxy @"int") (1::Integer)

int2 :: CompiledCode Integer
int2 = plc (Proxy @"int2") (2::Integer)

emptyBS :: CompiledCode Builtins.BuiltinByteString
emptyBS = plc (Proxy @"emptyBS") Builtins.emptyByteString

bool :: CompiledCode Bool
bool = plc (Proxy @"bool") True

andPlc :: CompiledCode (Bool -> Bool -> Bool)
andPlc = plc (Proxy @"andPlc") (\(x::Bool) (y::Bool) -> if x then (if y then True else False) else False)

tuple :: CompiledCode (Integer, Integer)
tuple = plc (Proxy @"tuple") (1::Integer, 2::Integer)

tupleMatch :: CompiledCode ((Integer, Integer) -> Integer)
tupleMatch = plc (Proxy @"tupleMatch") (\(x:: (Integer, Integer)) -> let (a, _) = x in a)

intCompare :: CompiledCode (Integer -> Integer -> Bool)
intCompare = plc (Proxy @"intCompare") (\(x::Integer) (y::Integer) -> Builtins.lessThanInteger x y)

intEq :: CompiledCode (Integer -> Integer -> Bool)
intEq = plc (Proxy @"intEq") (\(x::Integer) (y::Integer) -> Builtins.equalsInteger x y)

-- Has a Void in it
void :: CompiledCode (Integer -> Integer -> Bool)
void = plc (Proxy @"void") (\(x::Integer) (y::Integer) -> let a x' y' = case (x', y') of { (True, True) -> True; _ -> False; } in Builtins.equalsInteger x y `a` Builtins.equalsInteger y x)

intPlus :: CompiledCode (Integer -> Integer -> Integer)
intPlus = plc (Proxy @"intPlus") (\(x::Integer) (y::Integer) -> Builtins.addInteger x y)

intDiv :: CompiledCode (Integer -> Integer -> Integer)
intDiv = plc (Proxy @"intDiv") (\(x::Integer) (y::Integer) -> Builtins.divideInteger x y)

errorPlc :: CompiledCode (() -> Integer)
errorPlc = plc (Proxy @"errorPlc") (Builtins.error @Integer)

ifThenElse :: CompiledCode (Integer -> Integer -> Integer)
ifThenElse = plc (Proxy @"ifThenElse") (\(x::Integer) (y::Integer) -> if Builtins.equalsInteger x y then x else y)

emptyByteString :: CompiledCode (Builtins.BuiltinByteString -> Builtins.BuiltinByteString)
emptyByteString = plc (Proxy @"emptyByteString") (\(x :: Builtins.BuiltinByteString) -> x)

bytestring :: CompiledCode (Builtins.BuiltinByteString -> Builtins.BuiltinByteString)
bytestring = plc (Proxy @"bytestring") (\(x::Builtins.BuiltinByteString) -> x)

sha2 :: CompiledCode (Builtins.BuiltinByteString -> Builtins.BuiltinByteString)
sha2 = plc (Proxy @"sha2") (\(x :: Builtins.BuiltinByteString) -> Builtins.sha2_256 x)

bsEquals :: CompiledCode (Builtins.BuiltinByteString -> Builtins.BuiltinByteString -> Bool)
bsEquals = plc (Proxy @"bs32Equals") (\(x :: Builtins.BuiltinByteString) (y :: Builtins.BuiltinByteString) -> Builtins.equalsByteString x y)

bsLength :: CompiledCode (Builtins.BuiltinByteString -> Integer)
bsLength = plc (Proxy @"bs32Length") (\(x :: Builtins.BuiltinByteString) -> Builtins.lengthOfByteString x)

bsIndex :: CompiledCode (Builtins.BuiltinByteString -> Integer -> Integer)
bsIndex = plc (Proxy @"bs32Index") (\(x :: Builtins.BuiltinByteString) (n :: Integer) -> Builtins.indexByteString x n)

bsCons :: CompiledCode (Integer -> Builtins.BuiltinByteString -> Builtins.BuiltinByteString)
bsCons = plc (Proxy @"bs32Cons") (\(n :: Integer) (x :: Builtins.BuiltinByteString) -> Builtins.consByteString n x)

bsLt :: CompiledCode (Builtins.BuiltinByteString -> Builtins.BuiltinByteString -> Bool)
bsLt = plc (Proxy @"bsLt") (\(x :: Builtins.BuiltinByteString) (y :: Builtins.BuiltinByteString) -> Builtins.lessThanByteString x y)

bsDecode :: CompiledCode (Builtins.BuiltinByteString -> Builtins.BuiltinString)
bsDecode = plc (Proxy @"bsDecode") (\(x :: Builtins.BuiltinByteString) -> Builtins.decodeUtf8 x)

verify :: CompiledCode (Builtins.BuiltinByteString -> Builtins.BuiltinByteString -> Builtins.BuiltinByteString -> Bool)
verify = plc (Proxy @"verify") (\(x::Builtins.BuiltinByteString) (y::Builtins.BuiltinByteString) (z::Builtins.BuiltinByteString) -> Builtins.verifyEd25519Signature x y z)

trace :: CompiledCode (Builtins.BuiltinString -> ())
trace = plc (Proxy @"trace") (\(x :: Builtins.BuiltinString) -> Builtins.trace x ())

traceComplex :: CompiledCode (Bool -> ())
traceComplex = plc (Proxy @"traceComplex") (\(b :: Bool) -> if b then P.trace "yes" () else P.traceError "no")

stringLiteral :: CompiledCode (Builtins.BuiltinString)
stringLiteral = plc (Proxy @"stringLiteral") ("abc"::Builtins.BuiltinString)

stringEquals :: CompiledCode (Builtins.BuiltinString -> Builtins.BuiltinString -> Bool)
stringEquals = plc (Proxy @"string32Equals") (\(x :: Builtins.BuiltinString) (y :: Builtins.BuiltinString) -> Builtins.equalsString x y)

stringEncode :: CompiledCode (Builtins.BuiltinByteString)
stringEncode = plc (Proxy @"stringEncode") (Builtins.encodeUtf8 "abc")

dataEncode :: CompiledCode (Builtins.BuiltinData -> Builtins.BuiltinByteString)
dataEncode = plc (Proxy @"dataEncode") Builtins.serialiseData

constructData1 :: CompiledCode (Builtins.BuiltinData)
constructData1 = plc (Proxy @"constructData1") (Builtins.mkI 1)

deconstructData1 :: CompiledCode (Builtins.BuiltinData -> Integer)
deconstructData1 = plc (Proxy @"deconstructData1") (\(d :: Builtins.BuiltinData) -> Builtins.unsafeDataAsI d)

constructData2 :: CompiledCode (Builtins.BuiltinData)
constructData2 = plc (Proxy @"constructData2") (Builtins.mkConstr 1 [Builtins.mkI 2, Builtins.mkI 3])

deconstructData2 :: CompiledCode (Builtins.BuiltinData -> (Integer, [Integer]))
deconstructData2 = plc (Proxy @"deconstructData2") (\(d :: Builtins.BuiltinData) -> (P.fmap . P.fmap) Builtins.unsafeDataAsI (Builtins.unsafeDataAsConstr d))

constructData3 :: CompiledCode (Builtins.BuiltinData)
constructData3 = plc (Proxy @"constructData2") (Builtins.mkList [Builtins.mkI 2, Builtins.mkI 3])

deconstructData3 :: CompiledCode (Builtins.BuiltinData -> [Builtins.BuiltinData])
deconstructData3 = plc (Proxy @"deconstructData2") (\(d :: Builtins.BuiltinData) -> (Builtins.unsafeDataAsList d))

matchData1 :: CompiledCode (Builtins.BuiltinData -> Maybe Integer)
matchData1 = plc (Proxy @"matchData1") (\(d :: Builtins.BuiltinData) -> (Builtins.matchData d (\_ _ -> Nothing) (const Nothing) (const Nothing) (Just) (const Nothing)))
