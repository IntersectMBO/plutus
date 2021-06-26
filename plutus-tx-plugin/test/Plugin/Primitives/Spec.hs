{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}
{-# OPTIONS_GHC -fplugin PlutusTx.Plugin #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:defer-errors #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:debug-context #-}

module Plugin.Primitives.Spec where

import           Common
import           Lib
import           PlcTestUtils
import           Plugin.Lib

import qualified PlutusTx.Builtins          as Builtins
import qualified PlutusTx.Builtins.Class    as Builtins
import qualified PlutusTx.Builtins.Internal as BI
import           PlutusTx.Code
import           PlutusTx.Lift
import           PlutusTx.Plugin
import qualified PlutusTx.Prelude           as P

import qualified PlutusCore                 as PLC
import qualified PlutusCore.Default         as PLC

import           Data.Proxy

import           GHC.Magic

primitives :: TestNested
primitives = testNested "Primitives" [
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
  , goldenUEval "emptyByteStringApply" [ getPlc emptyByteString, liftProgram Builtins.emptyByteString ]
  , goldenPir "bytestring" bytestring
  , goldenUEval "bytestringApply" [ getPlc bytestring, liftProgram ("hello"::Builtins.ByteString) ]
  , goldenUEval "sha2_256" [ getPlc sha2, liftProgram ("hello" :: Builtins.ByteString)]
  , goldenUEval "equalsByteString" [ getPlc bsEquals, liftProgram ("hello" :: Builtins.ByteString), liftProgram ("hello" :: Builtins.ByteString)]
  , goldenUEval "ltByteString" [ getPlc bsLt, liftProgram ("hello" :: Builtins.ByteString), liftProgram ("world" :: Builtins.ByteString)]
  , goldenUEval "decodeUtf8" [ getPlc bsDecode, liftProgram ("hello" :: Builtins.ByteString)]
  , goldenPir "verify" verify
  , goldenPir "trace" trace
  , goldenPir "traceComplex" traceComplex
  , goldenPir "stringLiteral" stringLiteral
  , goldenPir "stringConvert" stringConvert
  , goldenUEval "equalsString" [ getPlc stringEquals, liftProgram ("hello" :: String), liftProgram ("hello" :: String)]
  , goldenPir "encodeUtf8" stringEncode
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

string :: CompiledCode String
string = plc (Proxy @"string") "test"

int :: CompiledCode Integer
int = plc (Proxy @"int") (1::Integer)

int2 :: CompiledCode Integer
int2 = plc (Proxy @"int2") (2::Integer)

emptyBS :: CompiledCode Builtins.ByteString
emptyBS = plc (Proxy @"emptyBS") Builtins.emptyByteString

bool :: CompiledCode Bool
bool = plc (Proxy @"bool") True

andPlc :: CompiledCode (Bool -> Bool -> Bool)
andPlc = plc (Proxy @"andPlc") (\(x::Bool) (y::Bool) -> if x then (if y then True else False) else False)

tuple :: CompiledCode (Integer, Integer)
tuple = plc (Proxy @"tuple") (1::Integer, 2::Integer)

tupleMatch :: CompiledCode ((Integer, Integer) -> Integer)
tupleMatch = plc (Proxy @"tupleMatch") (\(x:: (Integer, Integer)) -> let (a, b) = x in a)

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

emptyByteString :: CompiledCode (Builtins.ByteString -> Builtins.ByteString)
emptyByteString = plc (Proxy @"emptyByteString") (\(x :: Builtins.ByteString) -> x)

bytestring :: CompiledCode (Builtins.ByteString -> Builtins.ByteString)
bytestring = plc (Proxy @"bytestring") (\(x::Builtins.ByteString) -> x)

sha2 :: CompiledCode (Builtins.ByteString -> Builtins.ByteString)
sha2 = plc (Proxy @"sha2") (\(x :: Builtins.ByteString) -> Builtins.sha2_256 x)

bsEquals :: CompiledCode (Builtins.ByteString -> Builtins.ByteString -> Bool)
bsEquals = plc (Proxy @"bs32Equals") (\(x :: Builtins.ByteString) (y :: Builtins.ByteString) -> Builtins.equalsByteString x y)

bsLt :: CompiledCode (Builtins.ByteString -> Builtins.ByteString -> Bool)
bsLt = plc (Proxy @"bsLt") (\(x :: Builtins.ByteString) (y :: Builtins.ByteString) -> Builtins.lessThanByteString x y)

bsDecode :: CompiledCode (Builtins.ByteString -> Builtins.BuiltinString)
bsDecode = plc (Proxy @"bsDecode") (\(x :: Builtins.ByteString) -> Builtins.decodeUtf8 x)

verify :: CompiledCode (Builtins.ByteString -> Builtins.ByteString -> Builtins.ByteString -> Bool)
verify = plc (Proxy @"verify") (\(x::Builtins.ByteString) (y::Builtins.ByteString) (z::Builtins.ByteString) -> Builtins.verifySignature x y z)

trace :: CompiledCode (Builtins.BuiltinString -> ())
trace = plc (Proxy @"trace") (\(x :: Builtins.BuiltinString) -> Builtins.trace x ())

traceComplex :: CompiledCode (Bool -> ())
traceComplex = plc (Proxy @"traceComplex") (\(b :: Bool) -> if b then P.trace "yes" () else P.traceError "no")

stringLiteral :: CompiledCode (Builtins.BuiltinString)
stringLiteral = plc (Proxy @"stringLiteral") ("abc"::Builtins.BuiltinString)

stringConvert :: CompiledCode (Builtins.BuiltinString)
stringConvert = plc (Proxy @"stringConvert") ((noinline Builtins.stringToBuiltinString) "abc")

stringEquals :: CompiledCode (String -> String -> Bool)
stringEquals = plc (Proxy @"string32Equals") (\(x :: String) (y :: String) -> Builtins.equalsString (Builtins.stringToBuiltinString x) (Builtins.stringToBuiltinString y))

stringEncode :: CompiledCode (Builtins.ByteString)
stringEncode = plc (Proxy @"stringEncode") (Builtins.encodeUtf8 "abc")

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
