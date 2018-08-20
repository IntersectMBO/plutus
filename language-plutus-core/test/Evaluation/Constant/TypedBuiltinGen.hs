-- | This module defines the 'TypedBuiltinGen' type and functions of this type
-- which control size-induced bounds of values generated in the 'prop_applyBuiltinName'
-- function and its derivatives defined in the "Apply" module.

{-# LANGUAGE RankNTypes        #-}
{-# LANGUAGE GADTs             #-}
{-# LANGUAGE OverloadedStrings #-}
module Evaluation.Constant.TypedBuiltinGen
    ( TermOf(..)
    , TypedBuiltinGenT
    , TypedBuiltinGen
    , coerceTypedBuiltin
    , updateTypedBuiltinGenInt
    , updateTypedBuiltinGenBS
    , updateTypedBuiltinGenSize
    , updateTypedBuiltinGenBool
    , genTypedBuiltinFail
    , genTypedBuiltinDef
    , genTypedBuiltinLoose
    , genTypedBuiltinSum
    , genTypedBuiltinDiv
    , isqrt
    , iasqrt
    ) where

import           Language.PlutusCore
import           Language.PlutusCore.Constant

import           Data.Maybe
import           Data.Functor.Identity
import qualified Data.ByteString.Lazy as BSL
import           Data.Text.Prettyprint.Doc
import           Hedgehog hiding (Size, Var, annotate)
import qualified Hedgehog.Gen   as Gen
import qualified Hedgehog.Range as Range

-- | Coerce a Haskell value to a PLC value checking all constraints
-- (e.g. an 'Integer' is in appropriate bounds) along the way and
-- fail in case constraints are not satisfied.
coerceTypedBuiltin :: TypedBuiltin Size a -> a -> Value TyName Name ()
coerceTypedBuiltin tb x = fromMaybe err $ unsafeMakeConstant tb x where
    sx = prettyString $ TypedBuiltinValue tb x
    err = error $ "prop_typedAddInteger: out of bounds: " ++ sx

-- | A PLC 'Term' along with the correspoding Haskell value.
data TermOf a = TermOf
    { _termOfTerm  :: Term TyName Name ()  -- ^ The PLC term
    , _termOfValue :: a                    -- ^ The Haskell value.
    }
-- This has an interesting @Apply@ instance (no pun intended).

-- | A function of this type generates values of built-in typed (see 'TypedBuiltin' for
-- the list of such types) and returns it along with the corresponding PLC value.
-- Bounds induced (as per the spec) by the 'Size' values must be met, but can be narrowed.
type TypedBuiltinGenT m = forall a. TypedBuiltin Size a -> GenT m (TermOf a)

type TypedBuiltinGen = TypedBuiltinGenT Identity

instance Pretty a => Pretty (TermOf a) where
    pretty (TermOf t x) = pretty t <+> "~>" <+> pretty x

attachCoercedTerm :: Functor f => TypedBuiltin Size a -> GenT f a -> GenT f (TermOf a)
attachCoercedTerm tb = fmap $ \x -> TermOf (coerceTypedBuiltin tb x) x

-- TODO: think about abstracting the pattern... or maybe not.
updateTypedBuiltinGenInt
    :: Functor m => (Integer -> Integer -> GenT m Integer) -> TypedBuiltinGenT m -> TypedBuiltinGenT m
updateTypedBuiltinGenInt genInteger genTb tb = case tb of
    TypedBuiltinSized sizeEntry TypedBuiltinSizedInt ->
        let size = flattenSizeEntry sizeEntry
            (low, high) = toBoundsInt size in
            attachCoercedTerm tb $ genInteger low (high - 1)
    _                                                -> genTb tb

updateTypedBuiltinGenBS
    :: Monad m => (Int -> GenT m BSL.ByteString) -> TypedBuiltinGenT m -> TypedBuiltinGenT m
updateTypedBuiltinGenBS genBytes genTb tb = case tb of
    TypedBuiltinSized sizeEntry TypedBuiltinSizedBS ->
        let size = flattenSizeEntry sizeEntry in
            attachCoercedTerm tb . genBytes $ fromIntegral size
    _                                               -> genTb tb

updateTypedBuiltinGenSize
    :: Monad m => TypedBuiltinGenT m -> TypedBuiltinGenT m
updateTypedBuiltinGenSize genTb tb = case tb of
    TypedBuiltinSized sizeEntry TypedBuiltinSizedSize ->
        let size = flattenSizeEntry sizeEntry in
            attachCoercedTerm tb $ return size
    _                                                 -> genTb tb

updateTypedBuiltinGenBool
    :: Monad m => GenT m Bool -> TypedBuiltinGenT m -> TypedBuiltinGenT m
updateTypedBuiltinGenBool genBool genTb tb = case tb of
    TypedBuiltinBool -> attachCoercedTerm tb $ genBool
    _                -> genTb tb

-- | A built-ins generator that always fails.
genTypedBuiltinFail :: Monad m => TypedBuiltinGenT m
genTypedBuiltinFail tb = fail $ concat
    [ "A generator for the following builtin is not implemented: "
    , prettyString tb
    ]

-- | A default sized builtins generator that produces values in bounds seen in the spec.
genTypedBuiltinDef :: Monad m => TypedBuiltinGenT m
genTypedBuiltinDef
    = updateTypedBuiltinGenInt
          (\low high -> Gen.integral $ Range.linearFrom 0 low high)
    $ updateTypedBuiltinGenBS
          (fmap BSL.fromStrict . Gen.bytes . Range.linear 0)
    $ updateTypedBuiltinGenSize
    $ updateTypedBuiltinGenBool Gen.bool
    $ genTypedBuiltinFail

-- | A default sized builtins generator that produces values in bounds seen in the spec.
genTypedBuiltinLoose :: Monad m => TypedBuiltinGenT m
genTypedBuiltinLoose
    = updateTypedBuiltinGenInt
          (\low high -> Gen.integral $ Range.constantFrom 0 (iasqrt low `div` 2) (isqrt high `div` 2))
    $ updateTypedBuiltinGenBS
          (fmap BSL.fromStrict . Gen.bytes . Range.constant 0 . (`div` 3) . (* 2))
    $ genTypedBuiltinDef

-- | A sized builtins generator that produces 'Integer's in bounds narrowed by a factor of 2,
-- so one can use '(+)' or '(-)' over such integers without the risk of getting an overflow.
genTypedBuiltinSum :: Monad m => TypedBuiltinGenT m
genTypedBuiltinSum
    = updateTypedBuiltinGenInt
          (\low high -> Gen.integral $ Range.linear (low `div` 2) (high `div` 2))
    $ genTypedBuiltinDef

-- | A sized builtins generator that doesn't produce @0 :: Integer@,
-- so one case use 'div' or 'mod' over such integers without the risk of dividing by zero.
genTypedBuiltinDiv :: Monad m => TypedBuiltinGenT m
genTypedBuiltinDiv
    = updateTypedBuiltinGenInt
          (\low high -> Gen.filter (/= 0) . Gen.integral $ Range.linear low high)
    $ genTypedBuiltinDef

isqrt :: Integer -> Integer
isqrt n
    | n < 0     = error "isqrt: negative number"
    | n <= 1    = n
    | otherwise = head $ dropWhile (not . isRoot) iters
    where
        sqr = (^ (2 :: Int))
        twopows = iterate sqr 2
        (lowerRoot, lowerN) = last . takeWhile ((n >=) . snd) $ zip (1 : twopows) twopows
        newtonStep x = (x + n `div` x) `div` 2
        iters = iterate newtonStep $ isqrt (n `div` lowerN) * lowerRoot
        isRoot r = sqr r <= n && n < sqr (r + 1)

iasqrt :: Integer -> Integer
iasqrt n = signum n * isqrt (abs n)
