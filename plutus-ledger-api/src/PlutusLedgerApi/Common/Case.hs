{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE OverloadedStrings #-}

module PlutusLedgerApi.Common.Case (caseBuiltinDataUnavailable) where

import PlutusPrelude

import PlutusCore.Builtin
import PlutusCore.Default

import Data.Text (Text)
import Data.Vector qualified as Vector

{-| The built-in caser used after casing becomes available but before casing on 'Data'. Keeping
this as a first-order dispatcher lets the evaluation context select it once, without adding an
era check to the evaluator's casing path. -}
caseBuiltinDataUnavailable
  :: Some (ValueOf DefaultUni)
  -> Vector.Vector term
  -> HeadSpine Text term (Some (ValueOf DefaultUni))
caseBuiltinDataUnavailable someVal@(Some (ValueOf uni x)) branches = case uni of
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
{-# INLINE caseBuiltinDataUnavailable #-}

outOfBoundsErr :: Pretty a => a -> Vector.Vector term -> Text
outOfBoundsErr x branches =
  fold
    [ "'case "
    , display x
    , "' is out of bounds for the given number of branches: "
    , display $ Vector.length branches
    ]
