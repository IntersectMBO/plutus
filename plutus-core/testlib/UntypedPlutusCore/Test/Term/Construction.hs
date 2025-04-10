{-# OPTIONS_GHC -Wno-simplifiable-class-constraints #-}

module UntypedPlutusCore.Test.Term.Construction where

import Prelude
import UntypedPlutusCore

import Data.ByteString (ByteString)
import Data.Text (Text)
import Data.Text qualified as Text
import Data.Vector (Vector, fromList)
import PlutusCore.Crypto.BLS12_381.G1 qualified as BLS12_381.G1
import PlutusCore.Crypto.BLS12_381.G2 qualified as BLS12_381.G2
import PlutusCore.Crypto.BLS12_381.Pairing qualified as BLS12_381.Pairing
import PlutusCore.Data (Data)
import PlutusCore.Default (DefaultFun (..))
import Universe (Contains, someValue)

type T = Term Name DefaultUni DefaultFun ()

--------------------------------------------------------------------------------
-- Term construction -----------------------------------------------------------

name :: String -> Int -> Name
name n u = Name (Text.pack n) (Unique u)

var :: Name -> T
var = Var ()

lam :: Name -> T -> T
lam = LamAbs ()

app :: T -> T -> T
app = Apply ()

force :: T -> T
force = Force ()

delay :: T -> T
delay = Delay ()

err :: T
err = Error ()

ctor :: Word -> [T] -> T
ctor i = Constr () (fromIntegral i)

ctorTrue :: T
ctorTrue = ctor 0 []

ctorFalse :: T
ctorFalse = ctor 1 []

case_ :: T -> [T] -> T
case_ scrut branches = Case () scrut (fromList branches)

--------------------------------------------------------------------------------
-- Constants -------------------------------------------------------------------

constant :: (Contains DefaultUni a) => a -> T
constant = Constant () . someValue

int :: Integer -> T
int = constant

bytes :: ByteString -> T
bytes = constant

string :: Text -> T
string s = Constant () (someValue s)

unit :: T
unit = constant ()

true :: T
true = constant True

false :: T
false = constant False

array :: (Contains DefaultUni (Vector c)) => Vector c -> T
array = constant

list :: (Contains DefaultUni [c]) => [c] -> T
list = constant

pair :: (Contains DefaultUni a, Contains DefaultUni b) => a -> b -> T
pair x y = constant (x, y)

data_ :: Data -> T
data_ d = Constant () (someValue d)

bls12_381_G1 :: BLS12_381.G1.Element -> T
bls12_381_G1 = constant

bls12_381_G2 :: BLS12_381.G2.Element -> T
bls12_381_G2 = constant

bls12_381_MlResult :: BLS12_381.Pairing.MlResult -> T
bls12_381_MlResult = constant

--------------------------------------------------------------------------------
-- Builtins --------------------------------------------------------------------

builtin :: DefaultFun -> T
builtin = Builtin ()

addInteger :: T -> T -> T
addInteger i j = builtin AddInteger `app` i `app` j

subtractInteger :: T -> T -> T
subtractInteger i j = builtin SubtractInteger `app` i `app` j

multiplyInteger :: T -> T -> T
multiplyInteger i j = builtin MultiplyInteger `app` i `app` j

divideInteger :: T -> T -> T
divideInteger i j = builtin DivideInteger `app` i `app` j

quotientInteger :: T -> T -> T
quotientInteger i j = builtin QuotientInteger `app` i `app` j

remainderInteger :: T -> T -> T
remainderInteger i j = builtin RemainderInteger `app` i `app` j

modInteger :: T -> T -> T
modInteger i j = builtin ModInteger `app` i `app` j

equalsInteger :: T -> T -> T
equalsInteger i j = builtin EqualsInteger `app` i `app` j

lessThanInteger :: T -> T -> T
lessThanInteger i j = builtin LessThanInteger `app` i `app` j

lessThanEqualsInteger :: T -> T -> T
lessThanEqualsInteger i j = builtin LessThanEqualsInteger `app` i `app` j

appendByteString :: T -> T -> T
appendByteString b1 b2 = builtin AppendByteString `app` b1 `app` b2

consByteString :: T -> T -> T
consByteString i b = builtin ConsByteString `app` i `app` b

sliceByteString :: T -> T -> T -> T
sliceByteString start len bs =
  builtin SliceByteString `app` start `app` len `app` bs

lengthOfByteString :: T -> T
lengthOfByteString bs = builtin LengthOfByteString `app` bs

indexByteString :: T -> T -> T
indexByteString bs i = builtin IndexByteString `app` bs `app` i

equalsByteString :: T -> T -> T
equalsByteString b1 b2 = builtin EqualsByteString `app` b1 `app` b2

lessThanByteString :: T -> T -> T
lessThanByteString b1 b2 = builtin LessThanByteString `app` b1 `app` b2

lessThanEqualsByteString :: T -> T -> T
lessThanEqualsByteString b1 b2 =
  builtin LessThanEqualsByteString `app` b1 `app` b2

sha2_256 :: T -> T
sha2_256 bs = builtin Sha2_256 `app` bs

sha3_256 :: T -> T
sha3_256 bs = builtin Sha3_256 `app` bs

blake2b_256 :: T -> T
blake2b_256 bs = builtin Blake2b_256 `app` bs

verifyEd25519Signature :: T -> T -> T -> T
verifyEd25519Signature pk msg sig =
  builtin VerifyEd25519Signature `app` pk `app` msg `app` sig

verifyEcdsaSecp256k1Signature :: T -> T -> T -> T
verifyEcdsaSecp256k1Signature pk msg sig =
  builtin VerifyEcdsaSecp256k1Signature `app` pk `app` msg `app` sig

verifySchnorrSecp256k1Signature :: T -> T -> T -> T
verifySchnorrSecp256k1Signature pk msg sig =
  builtin VerifySchnorrSecp256k1Signature `app` pk `app` msg `app` sig

appendString :: T -> T -> T
appendString s1 s2 = builtin AppendString `app` s1 `app` s2

equalsString :: T -> T -> T
equalsString s1 s2 = builtin EqualsString `app` s1 `app` s2

encodeUtf8 :: T -> T
encodeUtf8 s = builtin EncodeUtf8 `app` s

decodeUtf8 :: T -> T
decodeUtf8 bs = builtin DecodeUtf8 `app` bs

ifThenElse :: T -> T -> T -> T
ifThenElse cond t f = force (builtin IfThenElse) `app` cond `app` t `app` f

chooseUnit :: T -> T -> T
chooseUnit unitVal x = force (builtin ChooseUnit) `app` unitVal `app` x

trace :: T -> T -> T
trace msg x = force (builtin Trace) `app` msg `app` x

fstPair :: T -> T
fstPair p = force (force (builtin FstPair)) `app` p

sndPair :: T -> T
sndPair p = force (force (builtin SndPair)) `app` p

chooseList :: T -> T -> T -> T
chooseList xs t f = force (builtin ChooseList) `app` xs `app` t `app` f

mkCons :: T -> T -> T
mkCons x xs = force (builtin MkCons) `app` x `app` xs

headList :: T -> T
headList xs = force (builtin HeadList) `app` xs

tailList :: T -> T
tailList xs = force (builtin TailList) `app` xs

nullList :: T -> T
nullList xs = force (builtin NullList) `app` xs

chooseData :: T -> T -> T -> T -> T -> T -> T
chooseData d constr m xs i b =
  force (builtin ChooseData)
    `app` d
    `app` constr
    `app` m
    `app` xs
    `app` i
    `app` b

constrData :: T -> T -> T
constrData i xs = builtin ConstrData `app` i `app` xs

mapData :: T -> T
mapData xs = builtin MapData `app` xs

listData :: T -> T
listData xs = builtin ListData `app` xs

iData :: T -> T
iData i = builtin IData `app` i

bData :: T -> T
bData bs = builtin BData `app` bs

unConstrData :: T -> T
unConstrData d = builtin UnConstrData `app` d

unMapData :: T -> T
unMapData d = builtin UnMapData `app` d

unListData :: T -> T
unListData d = builtin UnListData `app` d

unIData :: T -> T
unIData d = builtin UnIData `app` d

unBData :: T -> T
unBData d = builtin UnBData `app` d

equalsData :: T -> T -> T
equalsData d1 d2 = builtin EqualsData `app` d1 `app` d2

serialiseData :: T -> T
serialiseData d = builtin SerialiseData `app` d

mkPairData :: T -> T -> T
mkPairData d1 d2 = builtin MkPairData `app` d1 `app` d2

mkNilData :: T -> T
mkNilData unitVal = builtin MkNilData `app` unitVal

bls12_381_G1_add :: T -> T -> T
bls12_381_G1_add g1 g2 = builtin Bls12_381_G1_add `app` g1 `app` g2

bls12_381_G1_neg :: T -> T
bls12_381_G1_neg g1 = builtin Bls12_381_G1_neg `app` g1

bls12_381_G1_scalarMul :: T -> T -> T
bls12_381_G1_scalarMul scalar g1 =
  builtin Bls12_381_G1_scalarMul `app` scalar `app` g1

bls12_381_G1_equal :: T -> T -> T
bls12_381_G1_equal g1 g2 = builtin Bls12_381_G1_equal `app` g1 `app` g2

bls12_381_G1_hashToGroup :: T -> T -> T
bls12_381_G1_hashToGroup domain msg =
  builtin Bls12_381_G1_hashToGroup `app` domain `app` msg

bls12_381_G1_compress :: T -> T
bls12_381_G1_compress g1 = builtin Bls12_381_G1_compress `app` g1

bls12_381_G1_uncompress :: T -> T
bls12_381_G1_uncompress bs = builtin Bls12_381_G1_uncompress `app` bs

bls12_381_G2_add :: T -> T -> T
bls12_381_G2_add g2_1 g2_2 = builtin Bls12_381_G2_add `app` g2_1 `app` g2_2

bls12_381_G2_neg :: T -> T
bls12_381_G2_neg g2 = builtin Bls12_381_G2_neg `app` g2

bls12_381_G2_scalarMul :: T -> T -> T
bls12_381_G2_scalarMul scalar g2 =
  builtin Bls12_381_G2_scalarMul `app` scalar `app` g2

bls12_381_G2_equal :: T -> T -> T
bls12_381_G2_equal g2_1 g2_2 =
  builtin Bls12_381_G2_equal `app` g2_1 `app` g2_2

bls12_381_G2_hashToGroup :: T -> T -> T
bls12_381_G2_hashToGroup domain msg =
  builtin Bls12_381_G2_hashToGroup `app` domain `app` msg

bls12_381_G2_compress :: T -> T
bls12_381_G2_compress g2 =
  builtin Bls12_381_G2_compress `app` g2

bls12_381_G2_uncompress :: T -> T
bls12_381_G2_uncompress bs =
  builtin Bls12_381_G2_uncompress `app` bs

bls12_381_millerLoop :: T -> T -> T
bls12_381_millerLoop g1 g2 =
  builtin Bls12_381_millerLoop `app` g1 `app` g2

bls12_381_mulMlResult :: T -> T -> T
bls12_381_mulMlResult ml1 ml2 =
  builtin Bls12_381_mulMlResult `app` ml1 `app` ml2

bls12_381_finalVerify :: T -> T -> T
bls12_381_finalVerify ml1 ml2 =
  builtin Bls12_381_finalVerify `app` ml1 `app` ml2

mkNilPairData :: T -> T
mkNilPairData unitVal = builtin MkNilPairData `app` unitVal

keccak_256 :: T -> T
keccak_256 = app (builtin Keccak_256)

blake2b_224 :: T -> T
blake2b_224 = app (builtin Blake2b_224)

integerToByteString :: T -> T -> T -> T
integerToByteString signed endianness i =
  builtin IntegerToByteString `app` signed `app` endianness `app` i

byteStringToInteger :: T -> T -> T
byteStringToInteger signed bs =
  builtin ByteStringToInteger `app` signed `app` bs

andByteString :: T -> T -> T -> T
andByteString signed bs1 bs2 =
  builtin AndByteString `app` signed `app` bs1 `app` bs2

orByteString :: T -> T -> T -> T
orByteString signed bs1 bs2 =
  builtin OrByteString `app` signed `app` bs1 `app` bs2

xorByteString :: T -> T -> T -> T
xorByteString signed bs1 bs2 =
  builtin XorByteString `app` signed `app` bs1 `app` bs2

complementByteString :: T -> T
complementByteString bs =
  builtin ComplementByteString `app` bs

readBit :: T -> T -> T
readBit bs i =
  builtin ReadBit `app` bs `app` i

writeBits :: T -> T -> T -> T
writeBits bs indices bit =
  builtin WriteBits `app` bs `app` indices `app` bit

replicateByte :: T -> T -> T
replicateByte count byte =
  builtin ReplicateByte `app` count `app` byte

shiftByteString :: T -> T -> T
shiftByteString bs shift =
  builtin ShiftByteString `app` bs `app` shift

rotateByteString :: T -> T -> T
rotateByteString bs rotate =
  builtin RotateByteString `app` bs `app` rotate

countSetBits :: T -> T
countSetBits bs =
  builtin CountSetBits `app` bs

findFirstSetBit :: T -> T
findFirstSetBit bs =
  builtin FindFirstSetBit `app` bs

ripemd_160 :: T -> T
ripemd_160 bs =
  builtin Ripemd_160 `app` bs

expModInteger :: T -> T -> T -> T
expModInteger base ex modulus =
  builtin ExpModInteger `app` base `app` ex `app` modulus

caseList :: T -> T -> T -> T
caseList xs nilCase consCase =
  force (builtin CaseList) `app` xs `app` nilCase `app` consCase

caseData :: T -> T -> T -> T -> T -> T -> T
caseData d constrCase mapCase listCase iCase bCase =
  force (builtin CaseData)
    `app` d
    `app` constrCase
    `app` mapCase
    `app` listCase
    `app` iCase
    `app` bCase

dropList :: T -> T -> T
dropList n xs = force (builtin DropList) `app` n `app` xs

lengthOfArray :: T -> T
lengthOfArray xs = force (builtin LengthOfArray) `app` xs

listToArray :: T -> T
listToArray xs = force (builtin ListToArray) `app` xs

indexArray :: T -> T -> T
indexArray xs i = force (builtin IndexArray) `app` xs `app` i

--------------------------------------------------------------------------------
-- Unique names
--------------------------------------------------------------------------------

uniqueNames2
  :: String
  -> String
  -> (Name, Name)
uniqueNames2 n1 n2 =
  (name n1 0, name n2 1)

uniqueNames3
  :: String
  -> String
  -> String
  -> (Name, Name, Name)
uniqueNames3 n1 n2 n3 =
  (name n1 0, name n2 1, name n3 2)

uniqueNames4
  :: String
  -> String
  -> String
  -> String
  -> (Name, Name, Name, Name)
uniqueNames4 n1 n2 n3 n4 =
  (name n1 0, name n2 1, name n3 2, name n4 3)

uniqueNames5
  :: String
  -> String
  -> String
  -> String
  -> String
  -> (Name, Name, Name, Name, Name)
uniqueNames5 n1 n2 n3 n4 n5 =
  (name n1 0, name n2 1, name n3 2, name n4 3, name n5 4)

uniqueNames6
  :: String
  -> String
  -> String
  -> String
  -> String
  -> String
  -> (Name, Name, Name, Name, Name, Name)
uniqueNames6 n1 n2 n3 n4 n5 n6 =
  (name n1 0, name n2 1, name n3 2, name n4 3, name n5 4, name n6 5)

uniqueNames7
  :: String
  -> String
  -> String
  -> String
  -> String
  -> String
  -> String
  -> (Name, Name, Name, Name, Name, Name, Name)
uniqueNames7 n1 n2 n3 n4 n5 n6 n7 =
  (name n1 0, name n2 1, name n3 2, name n4 3, name n5 4, name n6 5, name n7 6)

uniqueNames8
  :: String
  -> String
  -> String
  -> String
  -> String
  -> String
  -> String
  -> String
  -> (Name, Name, Name, Name, Name, Name, Name, Name)
uniqueNames8 n1 n2 n3 n4 n5 n6 n7 n8 =
  ( name n1 0
  , name n2 1
  , name n3 2
  , name n4 3
  , name n5 4
  , name n6 5
  , name n7 6
  , name n8 7
  )
