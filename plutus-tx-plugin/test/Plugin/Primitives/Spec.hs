{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}
{-# OPTIONS -fplugin Language.PlutusTx.Plugin -fplugin-opt Language.PlutusTx.Plugin:defer-errors -fplugin-opt Language.PlutusTx.Plugin:debug-context #-}

module Plugin.Primitives.Spec where

import           Common
import           Lib
import           PlcTestUtils
import           Plugin.Lib

import qualified Language.PlutusTx.Builtins   as Builtins
import           Language.PlutusTx.Code
import           Language.PlutusTx.Lift
import           Language.PlutusTx.Plugin
import qualified Language.PlutusTx.Prelude    as P

import qualified Language.PlutusCore.Builtins as PLC
import qualified Language.PlutusCore.Universe as PLC

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
  , goldenPir "verify" verify
  , goldenPir "trace" trace
  , goldenPir "stringLiteral" stringLiteral
  , goldenPir "stringConvert" stringConvert
  ]

string :: CompiledCode PLC.DefaultUni PLC.DefaultFun String
string = plc (Proxy @"string") "test"

int :: CompiledCode PLC.DefaultUni PLC.DefaultFun Integer
int = plc (Proxy @"int") (1::Integer)

int2 :: CompiledCode PLC.DefaultUni PLC.DefaultFun Integer
int2 = plc (Proxy @"int2") (2::Integer)

emptyBS :: CompiledCode PLC.DefaultUni PLC.DefaultFun Builtins.ByteString
emptyBS = plc (Proxy @"emptyBS") Builtins.emptyByteString

bool :: CompiledCode PLC.DefaultUni PLC.DefaultFun Bool
bool = plc (Proxy @"bool") True

andPlc :: CompiledCode PLC.DefaultUni PLC.DefaultFun (Bool -> Bool -> Bool)
andPlc = plc (Proxy @"andPlc") (\(x::Bool) (y::Bool) -> if x then (if y then True else False) else False)

tuple :: CompiledCode PLC.DefaultUni PLC.DefaultFun (Integer, Integer)
tuple = plc (Proxy @"tuple") (1::Integer, 2::Integer)

tupleMatch :: CompiledCode PLC.DefaultUni PLC.DefaultFun ((Integer, Integer) -> Integer)
tupleMatch = plc (Proxy @"tupleMatch") (\(x:: (Integer, Integer)) -> let (a, b) = x in a)

intCompare :: CompiledCode PLC.DefaultUni PLC.DefaultFun (Integer -> Integer -> Bool)
intCompare = plc (Proxy @"intCompare") (\(x::Integer) (y::Integer) -> Builtins.lessThanInteger x y)

intEq :: CompiledCode PLC.DefaultUni PLC.DefaultFun (Integer -> Integer -> Bool)
intEq = plc (Proxy @"intEq") (\(x::Integer) (y::Integer) -> Builtins.equalsInteger x y)

-- Has a Void in it
void :: CompiledCode PLC.DefaultUni PLC.DefaultFun (Integer -> Integer -> Bool)
void = plc (Proxy @"void") (\(x::Integer) (y::Integer) -> let a x' y' = case (x', y') of { (True, True) -> True; _ -> False; } in Builtins.equalsInteger x y `a` Builtins.equalsInteger y x)

intPlus :: CompiledCode PLC.DefaultUni PLC.DefaultFun (Integer -> Integer -> Integer)
intPlus = plc (Proxy @"intPlus") (\(x::Integer) (y::Integer) -> Builtins.addInteger x y)

intDiv :: CompiledCode PLC.DefaultUni PLC.DefaultFun (Integer -> Integer -> Integer)
intDiv = plc (Proxy @"intDiv") (\(x::Integer) (y::Integer) -> Builtins.divideInteger x y)

errorPlc :: CompiledCode PLC.DefaultUni PLC.DefaultFun (() -> Integer)
errorPlc = plc (Proxy @"errorPlc") (Builtins.error @Integer)

ifThenElse :: CompiledCode PLC.DefaultUni PLC.DefaultFun (Integer -> Integer -> Integer)
ifThenElse = plc (Proxy @"ifThenElse") (\(x::Integer) (y::Integer) -> if Builtins.equalsInteger x y then x else y)

emptyByteString :: CompiledCode PLC.DefaultUni PLC.DefaultFun (Builtins.ByteString -> Builtins.ByteString)
emptyByteString = plc (Proxy @"emptyByteString") (\(x :: Builtins.ByteString) -> x)

bytestring :: CompiledCode PLC.DefaultUni PLC.DefaultFun (Builtins.ByteString -> Builtins.ByteString)
bytestring = plc (Proxy @"bytestring") (\(x::Builtins.ByteString) -> x)

sha2 :: CompiledCode PLC.DefaultUni PLC.DefaultFun (Builtins.ByteString -> Builtins.ByteString)
sha2 = plc (Proxy @"sha2") (\(x :: Builtins.ByteString) -> Builtins.sha2_256 x)

bsEquals :: CompiledCode PLC.DefaultUni PLC.DefaultFun (Builtins.ByteString -> Builtins.ByteString -> Bool)
bsEquals = plc (Proxy @"bs32Equals") (\(x :: Builtins.ByteString) (y :: Builtins.ByteString) -> Builtins.equalsByteString x y)

bsLt :: CompiledCode PLC.DefaultUni PLC.DefaultFun (Builtins.ByteString -> Builtins.ByteString -> Bool)
bsLt = plc (Proxy @"bsLt") (\(x :: Builtins.ByteString) (y :: Builtins.ByteString) -> Builtins.lessThanByteString x y)

verify :: CompiledCode PLC.DefaultUni PLC.DefaultFun (Builtins.ByteString -> Builtins.ByteString -> Builtins.ByteString -> Bool)
verify = plc (Proxy @"verify") (\(x::Builtins.ByteString) (y::Builtins.ByteString) (z::Builtins.ByteString) -> Builtins.verifySignature x y z)

trace :: CompiledCode PLC.DefaultUni PLC.DefaultFun (Builtins.String -> ())
trace = plc (Proxy @"trace") (\(x :: Builtins.String) -> Builtins.trace x)

stringLiteral :: CompiledCode PLC.DefaultUni PLC.DefaultFun (Builtins.String)
stringLiteral = plc (Proxy @"stringLiteral") ("abc"::Builtins.String)

stringConvert :: CompiledCode PLC.DefaultUni PLC.DefaultFun (Builtins.String)
stringConvert = plc (Proxy @"stringConvert") ((noinline P.stringToBuiltinString) "abc")
