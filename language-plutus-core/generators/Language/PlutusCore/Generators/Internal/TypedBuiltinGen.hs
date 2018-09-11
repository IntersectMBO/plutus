-- | This module defines the 'TypedBuiltinGen' type and functions of this type
-- which control size-induced bounds of values generated.
-- Big warning: generated terms do not satisfy the global uniqueness condition.

{-# LANGUAGE GADTs             #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes        #-}
module Language.PlutusCore.Generators.Internal.TypedBuiltinGen
    ( TermOf(..)
    , TypedBuiltinGenT
    , TypedBuiltinGen
    , genLowerBytes
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
import           PlutusPrelude

import qualified Data.ByteString.Lazy         as BSL
import           Data.Functor.Identity
import           Data.GADT.Compare
import           Hedgehog                     hiding (Size, Var)
import qualified Hedgehog.Gen                 as Gen
import qualified Hedgehog.Range               as Range

-- | Generate a UTF-8 lazy 'ByteString' containg lower-case letters.
genLowerBytes :: Monad m => Range Int -> GenT m BSL.ByteString
genLowerBytes range = BSL.fromStrict <$> Gen.utf8 range Gen.lower

-- | A PLC 'Term' along with the correspoding Haskell value.
data TermOf a = TermOf
    { _termOfTerm  :: Term TyName Name ()  -- ^ The PLC term
    , _termOfValue :: a                    -- ^ The Haskell value.
    } deriving (Functor)
-- This has an interesting @Apply@ instance (no pun intended).

-- | A function of this type generates values of built-in typed (see 'TypedBuiltin' for
-- the list of such types) and returns it along with the corresponding PLC value.
-- Bounds induced (as per the spec) by the 'Size' values must be met, but can be narrowed.
type TypedBuiltinGenT m = forall a. TypedBuiltin Size a -> GenT m (TermOf a)

-- | 'TypedBuiltinGenT' specified to 'Identity'.
type TypedBuiltinGen = TypedBuiltinGenT Identity

instance PrettyCfg a => PrettyCfg (TermOf a) where
    prettyCfg cfg (TermOf t x) = prettyCfg cfg t <+> "~>" <+> prettyCfg cfg x

attachCoercedTerm :: MonadQuote m => TypedBuiltin Size a -> GenT m a -> GenT m (TermOf a)
attachCoercedTerm tb genX = do
    x <- genX
    term <- liftQuote . unsafeMakeBuiltin $ TypedBuiltinValue tb x
    return $ TermOf term x

-- | Update a typed built-ins generator by overwriting the generator for a certain built-in.
updateTypedBuiltinGen
    :: MonadQuote m
    => TypedBuiltin Size a  -- ^ A generator of which built-in to overwrite.
    -> GenT m a             -- ^ A new generator.
    -> TypedBuiltinGenT m   -- ^ An old typed built-ins generator.
    -> TypedBuiltinGenT m   -- ^ The updated typed built-ins generator.
updateTypedBuiltinGen tbNew genX genTb tbOld
    | Just Refl <- tbNew `geq` tbOld = attachCoercedTerm tbOld genX
    | otherwise                      = genTb tbOld

-- | Update a sized typed built-ins generator by overwriting the generator for a certain built-in.
updateTypedBuiltinGenSized
    :: MonadQuote m
    => TypedBuiltinSized a  -- ^ A generator of which sized built-in to overwrite.
    -> (Size -> GenT m a)   -- ^ A function that computes new generator from a 'Size'.
    -> TypedBuiltinGenT m   -- ^ An old typed built-ins generator.
    -> TypedBuiltinGenT m   -- ^ The updated typed built-ins generator.
updateTypedBuiltinGenSized tbsNew genX genTb tbOld = case tbOld of
    TypedBuiltinSized se tbsOld | Just Refl <- tbsNew `geq` tbsOld ->
        attachCoercedTerm tbOld . genX $ flattenSizeEntry se
    _                                                              -> genTb tbOld

-- | Update a typed built-ins generator by overwriting the @integer@s generator.
updateTypedBuiltinGenInt
    :: MonadQuote m
    => (Integer -> Integer -> GenT m Integer) -> TypedBuiltinGenT m -> TypedBuiltinGenT m
updateTypedBuiltinGenInt genInteger =
    updateTypedBuiltinGenSized TypedBuiltinSizedInt $ \size ->
        let (low, high) = toBoundsInt size in
            genInteger low (high - 1)

-- | Update a typed built-ins generator by overwriting the @bytestring@s generator.
updateTypedBuiltinGenBS
    :: MonadQuote m
    => (Int -> GenT m BSL.ByteString) -> TypedBuiltinGenT m -> TypedBuiltinGenT m
updateTypedBuiltinGenBS genBytes =
    updateTypedBuiltinGenSized TypedBuiltinSizedBS $ genBytes . fromIntegral

-- | Update a typed built-ins generator by overwriting the @size@s generator.
updateTypedBuiltinGenSize
    :: MonadQuote m
    => TypedBuiltinGenT m -> TypedBuiltinGenT m
updateTypedBuiltinGenSize = updateTypedBuiltinGenSized TypedBuiltinSizedSize return

-- | Update a typed built-ins generator by overwriting the @boolean@s generator.
updateTypedBuiltinGenBool
    :: MonadQuote m
    => GenT m Bool -> TypedBuiltinGenT m -> TypedBuiltinGenT m
updateTypedBuiltinGenBool = updateTypedBuiltinGen TypedBuiltinBool

-- | A built-ins generator that always fails.
genTypedBuiltinFail :: Monad m => TypedBuiltinGenT m
genTypedBuiltinFail tb = fail $ fold
    [ "A generator for the following built-in is not implemented: "
    , prettyString tb
    ]

-- | A default sized builtins generator that produces values in bounds seen in the spec.
genTypedBuiltinDef :: MonadQuote m => TypedBuiltinGenT m
genTypedBuiltinDef
    = updateTypedBuiltinGenInt
          (\low high -> Gen.integral $ Range.linearFrom 0 low high)
    $ updateTypedBuiltinGenBS
          (genLowerBytes . Range.linear 0)
    $ updateTypedBuiltinGenSize
    $ updateTypedBuiltinGenBool Gen.bool
    $ genTypedBuiltinFail

-- | A default sized builtins generator that produces values in bounds seen in the spec.
genTypedBuiltinLoose :: MonadQuote m => TypedBuiltinGenT m
genTypedBuiltinLoose
    = updateTypedBuiltinGenInt
          (\low high -> Gen.integral $ Range.constantFrom 0 (iasqrt low `div` 2) (isqrt high `div` 2))
    $ updateTypedBuiltinGenBS
          (genLowerBytes . Range.constant 0 . (`div` 3) . (* 2))
    $ genTypedBuiltinDef

-- | A sized builtins generator that produces 'Integer's in bounds narrowed by a factor of 2,
-- so one can use '(+)' or '(-)' over such integers without the risk of getting an overflow.
genTypedBuiltinSum :: MonadQuote m => TypedBuiltinGenT m
genTypedBuiltinSum
    = updateTypedBuiltinGenInt
          (\low high -> Gen.integral $ Range.linear (low `div` 2) (high `div` 2))
    $ genTypedBuiltinDef

-- | A sized builtins generator that doesn't produce @0 :: Integer@,
-- so one case use 'div' or 'mod' over such integers without the risk of dividing by zero.
genTypedBuiltinDiv :: MonadQuote m => TypedBuiltinGenT m
genTypedBuiltinDiv
    = updateTypedBuiltinGenInt
          (\low high -> Gen.filter (/= 0) . Gen.integral $ Range.linear low high)
    $ genTypedBuiltinDef

-- | The integer square root.
-- Throws an 'error' on negative input.
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

-- | The integer square root that acts on negative numbers like this:
--
-- >>> iasqrt (-4)
-- -2
iasqrt :: Integer -> Integer
iasqrt n = signum n * isqrt (abs n)
