-- | This module defines the 'GenTypedBuiltin' type and functions of this type
-- which control size-induced bounds of values generated in the 'prop_applyBuiltinName'
-- function and its derivatives defined in the "Apply" module.

{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE GADTs      #-}
module Evaluation.Constant.GenTypedBuiltin
    ( TermOf(..)
    , GenTypedBuiltinT
    , GenTypedBuiltin
    , TheGenTypedBuiltinT(..)
    , coerceTypedBuiltin
    , updateGenTypedBuiltinInt
    , updateGenTypedBuiltinBS
    , updateGenTypedBuiltinSize
    , updateGenTypedBuiltinBool
    , genTypedBuiltinFail
    , genTypedBuiltinDef
    , genTypedBuiltinSum
    , genTypedBuiltinDiv
    ) where

import           Language.PlutusCore
import           Language.PlutusCore.Constant

import           Data.Maybe
import           Data.Functor.Identity
import qualified Data.ByteString.Lazy as BSL
import           Hedgehog hiding (Size, Var, annotate)
import qualified Hedgehog.Gen   as Gen
import qualified Hedgehog.Range as Range

-- | Coerce a Haskell value to a PLC value checking all constraints
-- (e.g. an 'Integer' is in appropriate bounds) along the way and
-- fail in case constraints are not satisfied.
coerceTypedBuiltin :: TypedBuiltin Size a -> a -> Value TyName Name ()
coerceTypedBuiltin tb x = fromMaybe err $ makeConstant tb x where
    sx = prettyString $ TypedBuiltinValue tb x
    err = error $ "prop_typedAddInteger: out of bounds: " ++ sx

-- This has an interesting @Apply@ instance (no pun intended).
data TermOf a = TermOf
    { _termOfTerm :: Term TyName Name ()
    , _termOfType :: a
    }

-- | A function of this type generates values of built-in typed (see 'TypedBuiltin' for
-- the list of such types) and returns it along with the corresponding PLC value.
-- Bounds induced (as per the spec) by the 'Size' values must be met, but can be narrowed.
type GenTypedBuiltinT m = forall a. TypedBuiltin Size a -> GenT m (TermOf a)

type GenTypedBuiltin = GenTypedBuiltinT Identity

newtype TheGenTypedBuiltinT m = TheGenTypedBuiltin
    { unTheAlltypedBuilinSized :: GenTypedBuiltinT m
    }

attachCoercedTerm :: Functor f => TypedBuiltin Size a -> GenT f a -> GenT f (TermOf a)
attachCoercedTerm tb = fmap $ \x -> TermOf (coerceTypedBuiltin tb x) x

-- TODO: think about abstracting the pattern... or maybe not.
updateGenTypedBuiltinInt
    :: Functor m
    => (Integer -> Integer -> GenT m Integer)
    -> GenTypedBuiltinT m
    -> GenTypedBuiltinT m
updateGenTypedBuiltinInt genInteger genTb tb = case tb of
    TypedBuiltinSized sizeEntry TypedBuiltinSizedInt ->
        let size = flattenSizeEntry sizeEntry
            (low, high) = toBoundsInt size in
            attachCoercedTerm tb $ genInteger low (high - 1)
    _                                                -> genTb tb

updateGenTypedBuiltinBS
    :: Monad m
    => (Int -> GenT m BSL.ByteString)
    -> GenTypedBuiltinT m
    -> GenTypedBuiltinT m
updateGenTypedBuiltinBS genBytes genTb tb = case tb of
    TypedBuiltinSized sizeEntry TypedBuiltinSizedBS ->
        let size = flattenSizeEntry sizeEntry in
            attachCoercedTerm tb . genBytes $ fromIntegral size
    _                                               -> genTb tb

updateGenTypedBuiltinSize
    :: Monad m
    => GenTypedBuiltinT m
    -> GenTypedBuiltinT m
updateGenTypedBuiltinSize genTb tb = case tb of
    TypedBuiltinSized sizeEntry TypedBuiltinSizedSize ->
        let size = flattenSizeEntry sizeEntry in
            attachCoercedTerm tb $ return size
    _                                               -> genTb tb

updateGenTypedBuiltinBool
    :: Monad m
    => GenT m Bool
    -> GenTypedBuiltinT m
    -> GenTypedBuiltinT m
updateGenTypedBuiltinBool genBool genTb tb = case tb of
    TypedBuiltinBool -> attachCoercedTerm tb $ genBool
    _                -> genTb tb

-- | A built-ins generator that always fails.
genTypedBuiltinFail :: Monad m => GenTypedBuiltinT m
genTypedBuiltinFail tb = fail $ concat
    [ "A generator for the following builtin is not implemented: "
    , prettyString tb
    ]

-- | A default sized builtins generator that produces values in bounds seen in the spec.
genTypedBuiltinDef :: Monad m => GenTypedBuiltinT m
genTypedBuiltinDef
    = updateGenTypedBuiltinInt
          (\low high -> Gen.integral $ Range.linear low high)
    $ updateGenTypedBuiltinBS
          (fmap BSL.fromStrict . Gen.bytes . Range.linear 0)
    $ updateGenTypedBuiltinSize
    $ genTypedBuiltinFail

-- | A sized builtins generator that produces 'Integer's in bounds narrowed by a factor of 2,
-- so one can use '(+)' or '(-)' over such integers without the risk of getting an overflow.
genTypedBuiltinSum :: Monad m => GenTypedBuiltinT m
genTypedBuiltinSum
    = updateGenTypedBuiltinInt
          (\low high -> Gen.integral $ Range.linear (low `div` 2) (high `div` 2))
    $ genTypedBuiltinDef

-- | A sized builtins generator that doesn't produce @0 :: Integer@,
-- so one case use 'div' or 'mod' over such integers without the risk of dividing by zero.
genTypedBuiltinDiv :: Monad m => GenTypedBuiltinT m
genTypedBuiltinDiv
    = updateGenTypedBuiltinInt
          (\low high -> Gen.filter (/= 0) . Gen.integral $ Range.linear low high)
    $ genTypedBuiltinDef
