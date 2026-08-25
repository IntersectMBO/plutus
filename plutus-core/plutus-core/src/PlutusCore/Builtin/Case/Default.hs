{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE OverloadedStrings #-}

module PlutusCore.Builtin.Case.Default (caseBuiltinNoData) where

import PlutusPrelude

import PlutusCore.Builtin
import PlutusCore.Default

import Data.Text (Text)
import Data.Vector qualified as Vector

-- | The built-in caser used when casing is available except on 'Data'.
caseBuiltinNoData
  :: Some (ValueOf DefaultUni)
  -> Vector.Vector term
  -> HeadSpine Text term (Some (ValueOf DefaultUni))
caseBuiltinNoData someVal@(Some (ValueOf uni x)) branches = case uni of
  DefaultUniUnit
    | 1 == len -> HeadOnly $ branches Vector.! 0
    | otherwise -> HeadError $ outOfBoundsErr someVal branches
  DefaultUniBool -> case x of
    False | len == 1 || len == 2 -> HeadOnly $ branches Vector.! 0
    True | len == 2 -> HeadOnly $ branches Vector.! 1
    _ -> HeadError $ outOfBoundsErr someVal branches
  DefaultUniInteger
    | 0 <= x && x < toInteger len -> HeadOnly $ branches Vector.! fromInteger x
    | otherwise -> HeadError $ outOfBoundsErr someVal branches
  DefaultUniData -> HeadError "Casing on data is not supported"
  DefaultUniList ty
    | len == 1 ->
        case x of
          [] -> HeadError "Expected non-empty list, got empty list for casing list"
          (y : ys) -> headSpine (branches Vector.! 0) [someValueOf ty y, someValueOf uni ys]
    | len == 2 ->
        case x of
          [] -> HeadOnly $ branches Vector.! 1
          (y : ys) -> headSpine (branches Vector.! 0) [someValueOf ty y, someValueOf uni ys]
    | otherwise -> HeadError $ outOfBoundsErr someVal branches
  DefaultUniPair tyL tyR
    | len == 1 ->
        case x of
          (l, r) -> headSpine (branches Vector.! 0) [someValueOf tyL l, someValueOf tyR r]
    | otherwise -> HeadError $ outOfBoundsErr someVal branches
  _ -> HeadError $ display uni <> " isn't supported in 'case'"
  where
    !len = Vector.length branches
{-# INLINE caseBuiltinNoData #-}

outOfBoundsErr :: Pretty a => a -> Vector.Vector term -> Text
outOfBoundsErr x branches =
  fold
    [ "'case "
    , display x
    , "' is out of bounds for the given number of branches: "
    , display $ Vector.length branches
    ]
