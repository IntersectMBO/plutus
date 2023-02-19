-- editorconfig-checker-disable-file
{-# LANGUAGE DataKinds         #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE TemplateHaskell   #-}
{-# LANGUAGE ViewPatterns      #-}

{-# OPTIONS_GHC -Wno-name-shadowing #-}

module PlutusBenchmark.BLS12_381.Common ( UProg
                                        , UTerm
                                        , checkGroth16Verify_Haskell
                                        , listOfSizedByteStrings
                                        , mkGroth16VerifyScript
                                        , mkHashAndAddG1Script
                                        , mkHashAndAddG2Script
                                        , mkPairingScript
                                        , mkUncompressAndAddG1Script
                                        , mkUncompressAndAddG2Script
                                        , toAnonDeBruijnProg
                                        )


where
import PlutusCore (DefaultFun, DefaultUni)
import PlutusTx qualified as Tx
import UntypedPlutusCore qualified as UPLC

import PlutusTx.Prelude as Tx hiding (sort, (*))

import Data.ByteString (ByteString)
import Data.ByteString qualified as BS
import Hedgehog.Internal.Gen qualified as G
import Hedgehog.Internal.Range qualified as R
import System.IO.Unsafe (unsafePerformIO)
import Text.Printf (printf)

import Prelude (IO, fromIntegral, show)


-------------------------------- PLC stuff--------------------------------

type UTerm   = UPLC.Term    UPLC.NamedDeBruijn DefaultUni DefaultFun ()
type UProg   = UPLC.Program UPLC.NamedDeBruijn DefaultUni DefaultFun ()
type UDBProg = UPLC.Program UPLC.DeBruijn      DefaultUni DefaultFun ()


compiledCodeToTerm
    :: Tx.CompiledCodeIn DefaultUni DefaultFun a -> UTerm
compiledCodeToTerm (Tx.getPlcNoAnn -> UPLC.Program _ _ body) = body

{- | Remove the textual names from a NamedDeBruijn program -}
toAnonDeBruijnProg :: UProg -> UDBProg
toAnonDeBruijnProg (UPLC.Program () ver body) =
    UPLC.Program () ver $ UPLC.termMapNames (\(UPLC.NamedDeBruijn _ ix) -> UPLC.DeBruijn ix) body

-- Create a list containing n bytestrings of length l.  This could be better.
listOfSizedByteStrings :: Integer -> Integer -> [ByteString]
listOfSizedByteStrings n l = unsafePerformIO . G.sample $
                             G.list (R.singleton $ fromIntegral n)
                                  (G.bytes (R.singleton $ fromIntegral l))


---------------- Examples ----------------

-- Hash some bytestrings onto G1 and add them all together

{-# INLINABLE hashAndAddG1 #-}
hashAndAddG1 :: [BuiltinByteString] -> BuiltinBLS12_381_G1_Element
hashAndAddG1 [] = error ()
hashAndAddG1 (p:ps) =
    go ps (Tx.bls12_381_G1_hashToCurve p)
    where go [] acc     = acc
          go (q:qs) acc = go qs $ Tx.bls12_381_G1_add (Tx.bls12_381_G1_hashToCurve q) acc

mkHashAndAddG1Script :: [ByteString] -> UProg
mkHashAndAddG1Script l =
    let points = map toBuiltin l
    in Tx.getPlcNoAnn $ $$(Tx.compile [|| hashAndAddG1 ||]) `Tx.applyCode` Tx.liftCode points

-- Hash some bytestrings onto G2 and add them all together

{-# INLINABLE hashAndAddG2 #-}
hashAndAddG2 :: [BuiltinByteString] -> BuiltinBLS12_381_G2_Element
hashAndAddG2 [] = error ()
hashAndAddG2 (p:ps) =
    go ps (Tx.bls12_381_G2_hashToCurve p)
    where go [] acc     = acc
          go (q:qs) acc = go qs $ Tx.bls12_381_G2_add (Tx.bls12_381_G2_hashToCurve q) acc

mkHashAndAddG2Script :: [ByteString] -> UProg
mkHashAndAddG2Script l =
    let points = map toBuiltin l
    in Tx.getPlcNoAnn $ $$(Tx.compile [|| hashAndAddG2 ||]) `Tx.applyCode` Tx.liftCode points

-- Deserialise a list of compressed G1 points and add them all together

{-# INLINABLE uncompressAndAddG1 #-}
uncompressAndAddG1 :: [BuiltinByteString] -> BuiltinBLS12_381_G1_Element
uncompressAndAddG1 [] = error ()
uncompressAndAddG1 (p:ps) =
    go ps (Tx.bls12_381_G1_uncompress p)
    where go [] acc     = acc
          go (q:qs) acc = go qs $ Tx.bls12_381_G1_add (Tx.bls12_381_G1_uncompress q) acc

mkUncompressAndAddG1Script :: [ByteString] -> UProg
mkUncompressAndAddG1Script l =
    let points = map (Tx.bls12_381_G1_compress . Tx.bls12_381_G1_hashToCurve . toBuiltin) l
    in Tx.getPlcNoAnn $ $$(Tx.compile [|| uncompressAndAddG1 ||]) `Tx.applyCode` Tx.liftCode points


-- Check that point addition is commutative in G1
checkUncompressAndAddG1_Haskell :: Integer -> IO ()
checkUncompressAndAddG1_Haskell n =
    let l = listOfSizedByteStrings 100 n
        points = map (Tx.bls12_381_G1_compress . Tx.bls12_381_G1_hashToCurve . toBuiltin) l
        result1 = uncompressAndAddG1 points
        result2 = uncompressAndAddG1 (reverse points)
    in do
      printf "%s\n" (show result1)
      printf "%s\n" (show result2)

-- Deserialise a list of compressed G1 points and add them all together

{-# INLINABLE uncompressAndAddG2 #-}
uncompressAndAddG2 :: [BuiltinByteString] -> BuiltinBLS12_381_G2_Element
uncompressAndAddG2 [] = error ()
uncompressAndAddG2 (p:ps) =
    go ps (Tx.bls12_381_G2_uncompress p)
    where go [] acc     = acc
          go (q:qs) acc = go qs $ Tx.bls12_381_G2_add (Tx.bls12_381_G2_uncompress q) acc

mkUncompressAndAddG2Script :: [ByteString] -> UProg
mkUncompressAndAddG2Script l =
    let points = map (Tx.bls12_381_G2_compress . Tx.bls12_381_G2_hashToCurve . toBuiltin) l
    in Tx.getPlcNoAnn $ $$(Tx.compile [|| uncompressAndAddG2 ||]) `Tx.applyCode` Tx.liftCode points

-- Check that point addition is commutative in G2
checkUncompressAndAddG2_Haskell :: Integer -> IO ()
checkUncompressAndAddG2_Haskell n =
    let l = listOfSizedByteStrings 100 n
        points = map (Tx.bls12_381_G2_compress . Tx.bls12_381_G2_hashToCurve . toBuiltin) l
        result1 = uncompressAndAddG2 points
        result2 = uncompressAndAddG2 (reverse points)
    in do
      printf "%s\n" (show result1)
      printf "%s\n" (show result2)

-- Pairing operations

{-# INLINABLE runPairingFunctions #-}
runPairingFunctions
    :: Tx.BuiltinBLS12_381_G1_Element
    -> Tx.BuiltinBLS12_381_G2_Element
    -> Tx.BuiltinBLS12_381_G1_Element
    -> Tx.BuiltinBLS12_381_G2_Element
    -> Bool
runPairingFunctions p1 p2 q1 q2 =
    let r1 = Tx.bls12_381_millerLoop p1 p2
        r2 = Tx.bls12_381_millerLoop q1 q2
    in Tx.bls12_381_finalVerify r1 r2

mkPairingScript
    :: BuiltinBLS12_381_G1_Element
    -> BuiltinBLS12_381_G2_Element
    -> BuiltinBLS12_381_G1_Element
    -> BuiltinBLS12_381_G2_Element
    -> UProg
mkPairingScript p1 p2 q1 q2 =
    Tx.getPlcNoAnn $ $$(Tx.compile [|| runPairingFunctions ||])
          `Tx.applyCode` Tx.liftCode p1
          `Tx.applyCode` Tx.liftCode p2
          `Tx.applyCode` Tx.liftCode q1
          `Tx.applyCode` Tx.liftCode q2

---------------- Groth16 verification ----------------

-- Wrappers for serialised group elements for slightly better type safety
newtype SerialisedG1Element = SerialisedG1Element { g1 :: BuiltinByteString }
    deriving newtype (Tx.Lift DefaultUni)

newtype SerialisedG2Element = SerialisedG2Element { g2 :: BuiltinByteString }
    deriving newtype (Tx.Lift DefaultUni)

scalar :: Integer
scalar = 11090173236178880413184798967381823895855059959147020707603928894861818263064

-- Lots of group elements for input to the computation

alpha :: SerialisedG1Element
alpha = SerialisedG1Element $ toBuiltin $ BS.pack [ 183, 29, 177, 250, 95, 65,
         54, 46, 147, 2, 91, 53, 86, 215, 110, 173, 18, 37, 207, 89, 13, 28,
         219, 158, 56, 42, 31, 235, 183, 150, 61, 205, 36, 165, 30, 24, 223, 4,
         171, 34, 27, 236, 175, 41, 22, 159, 175, 37]

alpha0 :: BuiltinByteString
alpha0 = toBuiltin $ BS.pack [ 183, 29, 177, 250, 95, 65,
         54, 46, 147, 2, 91, 53, 86, 215, 110, 173, 18, 37, 207, 89, 13, 28,
         219, 158, 56, 42, 31, 235, 183, 150, 61, 205, 36, 165, 30, 24, 223, 4,
         171, 34, 27, 236, 175, 41, 22, 159, 175, 37]


beta :: SerialisedG2Element
beta = SerialisedG2Element $ toBuiltin $ BS.pack [
        179, 162, 107, 11, 71, 18, 231, 141, 93, 113, 120, 109, 150, 19, 42, 124, 88, 80, 35,
        163, 102, 50, 202, 218, 68, 23, 26, 195, 244, 93, 181, 36, 195, 246, 87, 12, 138, 63,
        125, 236, 53, 174, 26, 195, 48, 155, 5, 221, 11, 48, 109, 180, 247, 79, 217, 236, 66,
        28, 167, 12, 84, 66, 93, 146, 46, 172, 76, 64, 59, 0, 219, 145, 111, 222, 223, 6, 91,
        220, 224, 14, 206, 23, 185, 122, 78, 151, 23, 62, 77, 89, 137, 129, 142, 223, 170, 76]

gamma :: SerialisedG2Element
gamma = SerialisedG2Element $ toBuiltin $ BS.pack [
         181, 172, 184, 0, 205, 73, 237, 140, 189, 219, 244, 145, 161, 252, 248, 171, 252, 147,
         240, 157, 56, 187, 178, 236, 182, 176, 142, 35, 164, 100, 44, 229, 156, 155, 3, 134,
         83, 154, 195, 206, 205, 251, 102, 169, 240, 39, 252, 33, 15, 37, 149, 16, 117, 100, 68,
         188, 94, 239, 101, 79, 77, 6, 18, 181, 214, 55, 95, 149, 38, 177, 185, 102, 206, 83,
         184, 241, 37, 148, 225, 179, 153, 208, 130, 49, 207, 230, 194, 105, 164, 74, 168, 213,
         135, 242, 54, 157]

delta :: SerialisedG2Element
delta = SerialisedG2Element $ toBuiltin $ BS.pack [
         179, 170, 121, 123, 175, 163, 154, 72, 246, 248, 124, 36, 131, 200, 148, 194, 129, 200,
         7, 130, 28, 71, 48, 31, 251, 117, 90, 207, 207, 210, 44, 35, 35, 206, 223, 99, 73, 199,
         254, 221, 50, 0, 164, 174, 85, 134, 49, 229, 1, 210, 153, 235, 147, 19, 92, 7, 207,
         105, 76, 161, 24, 209, 179, 134, 73, 5, 41, 198, 15, 87, 147, 92, 239, 168, 159, 202,
         250, 19, 168, 63, 132, 32, 123, 118, 254, 7, 141, 200, 89, 212, 2, 116, 61, 70, 140,
         21]

gamma_abc_1 :: SerialisedG1Element
gamma_abc_1 = SerialisedG1Element $ toBuiltin $ BS.pack [
               183, 246, 208, 109, 211, 229, 36, 110, 246, 181, 27, 7, 92, 48, 182, 143, 212, 144,
               251, 248, 94, 2, 5, 247, 159, 160, 77, 129, 19, 49, 146, 19, 148, 99, 181, 232, 239,
               178, 44, 57, 239, 61, 209, 197, 9, 32, 21, 184]

gamma_abc_2 :: SerialisedG1Element
gamma_abc_2 = SerialisedG1Element $ toBuiltin $ BS.pack [
               162, 230, 55, 219, 255, 82, 161, 228, 168, 197, 217, 133, 179, 65, 31, 197, 253, 68,
               175, 96, 126, 66, 146, 62, 171, 180, 122, 216, 118, 225, 240, 43, 91, 224, 52, 173,
               175, 115, 149, 42, 232, 175, 254, 229, 245, 24, 65, 222]

a :: SerialisedG1Element
a = SerialisedG1Element $ toBuiltin $ BS.pack [
     160, 91, 229, 15, 171, 87, 149, 187, 135, 132, 57, 58, 80, 69, 249, 135, 71, 23, 58,
     210, 135, 245, 94, 33, 52, 113, 189, 85, 151, 69, 85, 20, 82, 69, 60, 76, 58, 57, 231,
     200, 131, 16, 132, 159, 60, 122, 31, 195]

b :: SerialisedG2Element
b = SerialisedG2Element $ toBuiltin $ BS.pack [
     173, 99, 72, 182, 183, 179, 76, 134, 191, 55, 167, 72, 205, 45, 130, 162, 80, 223, 198,
     72, 70, 117, 102, 136, 37, 161, 111, 125, 166, 160, 77, 52, 36, 17, 62, 50, 92, 231,
     52, 236, 68, 149, 96, 130, 192, 160, 110, 95, 24, 104, 225, 241, 166, 229, 89, 185,
     254, 129, 241, 169, 1, 248, 166, 52, 27, 48, 28, 69, 178, 93, 48, 128, 251, 197, 3,
     147, 83, 216, 247, 27, 85, 11, 39, 78, 196, 192, 124, 112, 205, 17, 83, 86, 44, 49, 76,
     151]

c :: SerialisedG1Element
c = SerialisedG1Element $ toBuiltin $ BS.pack [
  181, 105, 204, 73, 27, 77, 240, 53, 203, 244, 158, 149, 31, 212, 254, 48, 170, 130, 54,
  176, 226, 175, 104, 244, 193, 89, 44, 212, 13, 235, 235, 113, 138, 243, 54, 57, 219,
  107, 193, 226, 218, 157, 152, 229, 83, 229, 234, 237]

{-# INLINABLE groth16Verify #-}
groth16Verify
    :: BuiltinByteString  -- G1
    -> BuiltinByteString  -- G2
    -> BuiltinByteString  -- G2
    -> BuiltinByteString  -- G1
    -> BuiltinByteString  -- G1
    -> BuiltinByteString  -- G1
    -> BuiltinByteString  -- G1
    -> BuiltinByteString  -- G2
    -> BuiltinByteString  -- G1
    -> Integer
    -> Bool
groth16Verify alpha' beta' gamma' delta' abc1' abc2' a' b' c' s =
    let alpha = Tx.bls12_381_G1_uncompress alpha'
        beta  = Tx.bls12_381_G2_uncompress beta'
        gamma = Tx.bls12_381_G2_uncompress gamma'
        delta = Tx.bls12_381_G2_uncompress delta'
        abc1  = Tx.bls12_381_G1_uncompress abc1'
        abc2  = Tx.bls12_381_G1_uncompress abc2'
        a     = Tx.bls12_381_G1_uncompress a'
        b     = Tx.bls12_381_G2_uncompress b'
        c     = Tx.bls12_381_G1_uncompress c'
        l1    = Tx.bls12_381_millerLoop    a b
        l2    = Tx.bls12_381_millerLoop    alpha beta
        l3    = Tx.bls12_381_millerLoop    c delta
        p     = Tx.bls12_381_G1_add        abc1 (Tx.bls12_381_G1_mul s abc2)
        l4    = Tx.bls12_381_millerLoop    p gamma
        y     = Tx.bls12_381_GT_mul        l2 (Tx.bls12_381_GT_mul l3 l4)
    in Tx.bls12_381_finalVerify l1 y

-- | Make a UPLC script applying groth16Verify to the inputs.  Passing the
-- newtype inputs increases the size and CPU cost slightly, so we unwrap them
-- first.  This should return `True`.
mkGroth16VerifyScript :: UProg
mkGroth16VerifyScript =
    Tx.getPlcNoAnn $ $$(Tx.compile [|| groth16Verify ||])
           `Tx.applyCode` (Tx.liftCode $ g1 alpha)
           `Tx.applyCode` (Tx.liftCode $ g2 beta)
           `Tx.applyCode` (Tx.liftCode $ g2 gamma)
           `Tx.applyCode` (Tx.liftCode $ g2 delta)
           `Tx.applyCode` (Tx.liftCode $ g1 gamma_abc_1)
           `Tx.applyCode` (Tx.liftCode $ g1 gamma_abc_2)
           `Tx.applyCode` (Tx.liftCode $ g1 a)
           `Tx.applyCode` (Tx.liftCode $ g2 b)
           `Tx.applyCode` (Tx.liftCode $ g1 c)
           `Tx.applyCode` Tx.liftCode scalar

-- | Check that the Haskell version returns the correct result.
checkGroth16Verify_Haskell :: Bool
checkGroth16Verify_Haskell =
    groth16Verify (g1 alpha) (g2 beta) (g2 gamma) (g2 delta)
                      (g1 gamma_abc_1) (g1 gamma_abc_2) (g1 a) (g2 b) (g1 c) scalar

