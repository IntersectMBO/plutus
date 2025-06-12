-- Copyright 2025 Lennart Augustsson
-- See LICENSE file for full license.
module MicroHs.Names where
import MHSPrelude
import MicroHs.Ident
import Prelude qualified ()

-- Identifiers known by the compiler.

builtinLoc :: SLoc
builtinLoc = SLoc "builtin" 0 0

mkIdentB :: String -> Ident
mkIdentB = mkIdentSLoc builtinLoc

boolPrefix :: String
boolPrefix = "Data.Bool_Type."

listPrefix :: String
listPrefix = "Data.List_Type."

nameList :: String
nameList = listPrefix ++ "[]"
identList :: Ident
identList = mkIdentB nameList

nameInt :: String
nameInt = "Primitives.Int"
identInt :: Ident
identInt = mkIdentB nameInt

nameWord :: String
nameWord = "Primitives.Word"
identWord :: Ident
identWord = mkIdentB nameWord

nameFloatW :: String
nameFloatW = "Primitives.FloatW"
identFloatW :: Ident
identFloatW = mkIdentB nameFloatW

nameChar :: String
nameChar = "Primitives.Char"
identChar :: Ident
identChar = mkIdentB nameChar

nameInteger :: String
nameInteger = "Data.Integer_Type.Integer"
identInteger :: Ident
identInteger = mkIdentB nameInteger

nameTypeEq :: String
nameTypeEq = "Primitives.~"
identTypeEq :: Ident
identTypeEq = mkIdentB nameTypeEq

nameImplies :: String
nameImplies = "Primitives.=>"
identImplies :: Ident
identImplies = mkIdentB nameImplies

nameArrow :: String
nameArrow = "Primitives.->"
identArrow :: Ident
identArrow = mkIdentB nameArrow

nameSymbol :: String
nameSymbol = "Primitives.Symbol"

nameNat :: String
nameNat = "Primitives.Nat"

nameType :: String
nameType = "Primitives.Type"

nameKind :: String
nameKind = "Primitives.Kind"

nameConstraint :: String
nameConstraint = "Primitives.Constraint"

nameKnownNat :: String
nameKnownNat = "Data.TypeLits.KnownNat"

nameKnownSymbol :: String
nameKnownSymbol = "Data.TypeLits.KnownSymbol"

nameCoercible :: String
nameCoercible = "Data.Coerce.Coercible"

nameHasField :: String
nameHasField = "Data.Records.HasField"

nameSetField :: String
nameSetField = "Data.Records.SetField"

namegetField :: String
namegetField = "getField"

namesetField :: String
namesetField = "setField"

nameByteString :: String
nameByteString = "Data.ByteString.Internal.ByteString"
identByteString :: Ident
identByteString = mkIdentB nameByteString

identIO :: Ident
identIO = mkIdentB "Primitives.IO"

identUnit :: Ident
identUnit = mkIdentB "()"

identPtr :: Ident
identPtr = mkIdentB "Primitives.Ptr"

identFunPtr :: Ident
identFunPtr = mkIdentB "Primitives.FunPtr"

-----

instPrefix :: String
instPrefix = "inst"

uniqIdentSep :: String
uniqIdentSep = "$"

-- Needed dictionaries
dictPrefix :: String
dictPrefix = "dict"

dictPrefixDollar :: String
dictPrefixDollar = dictPrefix ++ uniqIdentSep

-- Dictionary argument names
adictPrefix :: String
adictPrefix = "adict"
