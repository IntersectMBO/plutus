{-# LANGUAGE ScopedTypeVariables #-}

{-# OPTIONS -Wall #-}







module PlutusCore.BuiltinEvaluation where

import PlutusCore.Term
import Utils.ABT
import Utils.Pretty

import Crypto.Hash
import qualified Crypto.Sign.Ed25519 as Ed25519 ()
import qualified Data.Binary as B
import qualified Data.ByteArray as BA
import qualified Data.ByteString.Lazy as BS
import Data.List (intercalate)







builtin :: String
        -> [Term]
        -> Either String Term
builtin "addInt" xs =
  case xs of
    [In (PrimData (PrimInt x)), In (PrimData (PrimInt y))] ->
      Right $ In (PrimData (PrimInt (x + y)))
    _ ->
      Left $ "Incorrect arguments for builtin addInt: "
                ++ intercalate "," (map pretty xs)
builtin "subtractInt" xs =
  case xs of
    [In (PrimData (PrimInt x)), In (PrimData (PrimInt y))] ->
      Right $ In (PrimData (PrimInt (x - y)))
    _ ->
      Left $ "Incorrect arguments for builtin subtractInt: "
                ++ intercalate "," (map pretty xs)
builtin "multiplyInt" xs =
  case xs of
    [In (PrimData (PrimInt x)), In (PrimData (PrimInt y))] ->
      Right $ In (PrimData (PrimInt (x * y)))
    _ ->
      Left $ "Incorrect arguments for builtin multiplyInt: "
                ++ intercalate "," (map pretty xs)
builtin "divideInt" xs =
  case xs of
    [In (PrimData (PrimInt x)), In (PrimData (PrimInt y))] ->
      Right $ In (PrimData (PrimInt (div x y)))
    _ ->
      Left $ "Incorrect arguments for builtin divideInt: "
                ++ intercalate "," (map pretty xs)
builtin "remainderInt" xs =
  case xs of
    [In (PrimData (PrimInt x)), In (PrimData (PrimInt y))] ->
      Right $ In (PrimData (PrimInt (mod x y)))
    _ ->
      Left $ "Incorrect arguments for builtin remainderInt: "
                ++ intercalate "," (map pretty xs)
builtin "lessThanInt" xs =
  case xs of
    [In (PrimData (PrimInt x)), In (PrimData (PrimInt y))] ->
      Right $ if x < y then conH "True" [] else conH "False" []
    _ ->
      Left $ "Incorrect arguments for builtin lessThanInt: "
                ++ intercalate "," (map pretty xs)
builtin "equalsInt" xs =
  case xs of
    [In (PrimData (PrimInt x)), In (PrimData (PrimInt y))] ->
      Right $ if x == y then conH "True" [] else conH "False" []
    _ ->
      Left $ "Incorrect arguments for builtin equalsInt: "
                ++ intercalate "," (map pretty xs)
builtin "intToFloat" xs =
  case xs of
    [In (PrimData (PrimInt x))] ->
      Right $ In (PrimData (PrimFloat (fromInteger (toInteger x))))
    _ ->
      Left $ "Incorrect arguments for builtin intToFloat: "
                ++ intercalate "," (map pretty xs)
builtin "intToByteString" xs =
  case xs of
    [In (PrimData (PrimInt x))] ->
      Right $ In (PrimData (PrimByteString (B.encode x)))
    _ ->
      Left
        $ "Incorrect arguments for builtin intToBytestring: "
       ++ intercalate "," (map pretty xs)
builtin "addFloat" xs =
  case xs of
    [In (PrimData (PrimFloat x)), In (PrimData (PrimFloat y))] ->
      Right $ In (PrimData (PrimFloat (x + y)))
    _ ->
      Left $ "Incorrect arguments for builtin addFloat: "
                ++ intercalate "," (map pretty xs)
builtin "subtractFloat" xs =
  case xs of
    [In (PrimData (PrimFloat x)), In (PrimData (PrimFloat y))] ->
      Right $ In (PrimData (PrimFloat (x - y)))
    _ ->
      Left $ "Incorrect arguments for builtin subtractFloat: "
                ++ intercalate "," (map pretty xs)  
builtin "multiplyFloat" xs =
  case xs of
    [In (PrimData (PrimFloat x)), In (PrimData (PrimFloat y))] ->
      Right $ In (PrimData (PrimFloat (x * y)))
    _ ->
      Left $ "Incorrect arguments for builtin multiplyFloat: "
                ++ intercalate "," (map pretty xs)
builtin "divideFloat" xs =
  case xs of
    [In (PrimData (PrimFloat x)), In (PrimData (PrimFloat y))] ->
      Right $ In (PrimData (PrimFloat (x / y)))
    _ ->
      Left $ "Incorrect arguments for builtin divideFloat: "
                ++ intercalate "," (map pretty xs)
builtin "lessThanFloat" xs =
  case xs of
    [In (PrimData (PrimFloat x)), In (PrimData (PrimFloat y))] ->
      Right $ if x < y then conH "True" [] else conH "False" []
    _ ->
      Left $ "Incorrect arguments for builtin lessThanFloat: "
                ++ intercalate "," (map pretty xs)
builtin "equalsFloat" xs =
  case xs of
    [In (PrimData (PrimFloat x)), In (PrimData (PrimFloat y))] ->
      Right $ if x == y then conH "True" [] else conH "False" []
    _ ->
      Left $ "Incorrect arguments for builtin equalsFloat: "
                ++ intercalate "," (map pretty xs)
builtin "ceiling" xs =
  case xs of
    [In (PrimData (PrimFloat x))] ->
      Right $ In (PrimData (PrimInt (ceiling x)))
    _ ->
      Left $ "Incorrect arguments for builtin ceiling: "
                ++ intercalate "," (map pretty xs)
builtin "floor" xs =
  case xs of
    [In (PrimData (PrimFloat x))] ->
      Right $ In (PrimData (PrimInt (floor x)))
    _ ->
      Left $ "Incorrect arguments for builtin floor: "
                ++ intercalate "," (map pretty xs)
builtin "round" xs =
  case xs of
    [In (PrimData (PrimFloat x))] ->
      Right $ In (PrimData (PrimInt (round x)))
    _ ->
      Left $ "Incorrect arguments for builtin round: "
                ++ intercalate "," (map pretty xs)
builtin "concatenate" xs =
  case xs of
    [ In (PrimData (PrimByteString x))
      , In (PrimData (PrimByteString y))
      ] ->
      Right $ In (PrimData (PrimByteString (BS.concat [x,y])))
    _ ->
      Left $ "Incorrect arguments for builtin concatenate: "
                ++ intercalate "," (map pretty xs)
builtin "drop" xs =
  case xs of
    [ In (PrimData (PrimInt x))
      , In (PrimData (PrimByteString y))
      ] ->
      Right $ In (PrimData (PrimByteString (BS.drop (fromIntegral x) y)))
    _ ->
      Left $ "Incorrect arguments for builtin drop: "
                ++ intercalate "," (map pretty xs)
builtin "take" xs =
  case xs of
    [ In (PrimData (PrimInt x))
      , In (PrimData (PrimByteString y))
      ] ->
      Right $ In (PrimData (PrimByteString (BS.take (fromIntegral x) y)))
    _ ->
      Left $ "Incorrect arguments for builtin take: "
                ++ intercalate "," (map pretty xs)
builtin "equalsByteString" xs =
  case xs of
    [ In (PrimData (PrimByteString x))
      , In (PrimData (PrimByteString y))
      ] ->
      Right $ if x == y then conH "True" [] else conH "False" []
    _ ->
      Left $ "Incorrect arguments for builtin equalsByteString: "
                ++ intercalate "," (map pretty xs)     
builtin "sha2_256"    xs = hashBuiltin "sha2_256" SHA256 xs
builtin "sha3_256"    xs = hashBuiltin "sha3_256" SHA3_256 xs
builtin "blake2b_224" xs = hashBuiltin "blake2b_224" Blake2b_224 xs
builtin n _ =
  Left $ "No builtin named " ++ n

hashBuiltin :: forall algo. HashAlgorithm algo
            => String
            -> algo
            -> [Term]
            -> Either String Term
hashBuiltin builtinName algo xs =
  case xs of
    [In (PrimData (PrimByteString x))] ->
      Right $ In (PrimData
                    (PrimByteString
                      (BS.pack
                        (BA.unpack (hash (BS.toStrict x) :: Digest algo)))))
    _ ->
      Left $ "Incorrect arguments for builtin " ++ builtinName ++ ": "
                ++ intercalate "," (map pretty xs)

