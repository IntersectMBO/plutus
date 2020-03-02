{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}
{-# OPTIONS -fplugin Language.PlutusTx.Plugin -fplugin-opt Language.PlutusTx.Plugin:defer-errors -fplugin-opt Language.PlutusTx.Plugin:no-context #-}

module Plugin.Primitives.Spec where

import           Common
import           PlcTestUtils
import           Plugin.Lib

import qualified Language.PlutusTx.Builtins   as Builtins
import           Language.PlutusTx.Code
import           Language.PlutusTx.Lift
import           Language.PlutusTx.Plugin

import qualified Language.PlutusCore.Universe as PLC

-- this module does lots of weird stuff deliberately
{-# ANN module ("HLint: ignore"::String) #-}

primitives :: TestNested
primitives = testNested "Primitives" [
    goldenPir "string" string
  , goldenPir "int" int
  , goldenPir "int2" int2
  , goldenPir "bool" bool
  , goldenPir "and" andPlc
  , goldenEval "andApply" [ getProgram andPlc, getProgram $ plc @"T" True, getProgram $ plc @"F" False ]
  , goldenPir "tuple" tuple
  , goldenPir "tupleMatch" tupleMatch
  , goldenEval "tupleConstDest" [ getProgram tupleMatch, getProgram tuple ]
  , goldenPir "intCompare" intCompare
  , goldenPir "intEq" intEq
  , goldenEval "intEqApply" [ getProgram intEq, getProgram int, getProgram int ]
  , goldenPir "void" void
  , goldenPir "intPlus" intPlus
  , goldenPir "intDiv" intDiv
  , goldenEval "intPlusApply" [ getProgram intPlus, getProgram int, getProgram int2 ]
  , goldenPir "error" errorPlc
  , goldenPir "ifThenElse" ifThenElse
  , goldenEval "ifThenElseApply" [ getProgram ifThenElse, getProgram int, getProgram int2 ]
  , goldenPir "emptyByteString" emptyByteString
  , goldenEval "emptyByteStringApply" [ getPlc emptyByteString, liftProgram Builtins.emptyByteString ]
  , goldenPir "bytestring" bytestring
  , goldenEval "bytestringApply" [ getPlc bytestring, liftProgram ("hello"::Builtins.ByteString) ]
  , goldenEval "sha2_256" [ getPlc sha2, liftProgram ("hello" :: Builtins.ByteString)]
  , goldenEval "equalsByteString" [ getPlc bsEquals, liftProgram ("hello" :: Builtins.ByteString), liftProgram ("hello" :: Builtins.ByteString)]
  , goldenEval "ltByteString" [ getPlc bsLt, liftProgram ("hello" :: Builtins.ByteString), liftProgram ("world" :: Builtins.ByteString)]
  , goldenPir "verify" verify
  , goldenPir "trace" trace
  ]

string :: CompiledCode PLC.DefaultUni String
string = plc @"string" "test"

int :: CompiledCode PLC.DefaultUni Integer
int = plc @"int" (1::Integer)

int2 :: CompiledCode PLC.DefaultUni Integer
int2 = plc @"int2" (2::Integer)

emptyBS :: CompiledCode PLC.DefaultUni Builtins.ByteString
emptyBS = plc @"emptyBS" Builtins.emptyByteString

bool :: CompiledCode PLC.DefaultUni Bool
bool = plc @"bool" True

andPlc :: CompiledCode PLC.DefaultUni (Bool -> Bool -> Bool)
andPlc = plc @"andPlc" (\(x::Bool) (y::Bool) -> if x then (if y then True else False) else False)

tuple :: CompiledCode PLC.DefaultUni (Integer, Integer)
tuple = plc @"tuple" (1::Integer, 2::Integer)

tupleMatch :: CompiledCode PLC.DefaultUni ((Integer, Integer) -> Integer)
tupleMatch = plc @"tupleMatch" (\(x:: (Integer, Integer)) -> let (a, b) = x in a)

intCompare :: CompiledCode PLC.DefaultUni (Integer -> Integer -> Bool)
intCompare = plc @"intCompare" (\(x::Integer) (y::Integer) -> Builtins.lessThanInteger x y)

intEq :: CompiledCode PLC.DefaultUni (Integer -> Integer -> Bool)
intEq = plc @"intEq" (\(x::Integer) (y::Integer) -> Builtins.equalsInteger x y)

-- Has a Void in it
void :: CompiledCode PLC.DefaultUni (Integer -> Integer -> Bool)
void = plc @"void" (\(x::Integer) (y::Integer) -> let a x' y' = case (x', y') of { (True, True) -> True; _ -> False; } in Builtins.equalsInteger x y `a` Builtins.equalsInteger y x)

intPlus :: CompiledCode PLC.DefaultUni (Integer -> Integer -> Integer)
intPlus = plc @"intPlus" (\(x::Integer) (y::Integer) -> Builtins.addInteger x y)

intDiv :: CompiledCode PLC.DefaultUni (Integer -> Integer -> Integer)
intDiv = plc @"intDiv" (\(x::Integer) (y::Integer) -> Builtins.divideInteger x y)

errorPlc :: CompiledCode PLC.DefaultUni (() -> Integer)
errorPlc = plc @"errorPlc" (Builtins.error @Integer)

ifThenElse :: CompiledCode PLC.DefaultUni (Integer -> Integer -> Integer)
ifThenElse = plc @"ifThenElse" (\(x::Integer) (y::Integer) -> if Builtins.equalsInteger x y then x else y)

emptyByteString :: CompiledCode PLC.DefaultUni (Builtins.ByteString -> Builtins.ByteString)
emptyByteString = plc @"emptyByteString" (\(x :: Builtins.ByteString) -> x)

bytestring :: CompiledCode PLC.DefaultUni (Builtins.ByteString -> Builtins.ByteString)
bytestring = plc @"bytestring" (\(x::Builtins.ByteString) -> x)

sha2 :: CompiledCode PLC.DefaultUni (Builtins.ByteString -> Builtins.ByteString)
sha2 = plc @"sha2" (\(x :: Builtins.ByteString) -> Builtins.sha2_256 x)

bsEquals :: CompiledCode PLC.DefaultUni (Builtins.ByteString -> Builtins.ByteString -> Bool)
bsEquals = plc @"bs32Equals" (\(x :: Builtins.ByteString) (y :: Builtins.ByteString) -> Builtins.equalsByteString x y)

bsLt :: CompiledCode PLC.DefaultUni (Builtins.ByteString -> Builtins.ByteString -> Bool)
bsLt = plc @"bsLt" (\(x :: Builtins.ByteString) (y :: Builtins.ByteString) -> Builtins.lessThanByteString x y)

verify :: CompiledCode PLC.DefaultUni (Builtins.ByteString -> Builtins.ByteString -> Builtins.ByteString -> Bool)
verify = plc @"verify" (\(x::Builtins.ByteString) (y::Builtins.ByteString) (z::Builtins.ByteString) -> Builtins.verifySignature x y z)

trace :: CompiledCode PLC.DefaultUni (Builtins.String -> ())
trace = plc @"trace" (\(x :: Builtins.String) -> Builtins.trace x)
