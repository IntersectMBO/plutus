-- | This module defines the 'TypedBuiltinGen' type and functions of this type
-- which control size-induced bounds of values generated.

{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE UndecidableInstances  #-}

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
    , genTypedBuiltinOutOfBounds
    , genTypedBuiltinSmall
    , genTypedBuiltinSum
    , genTypedBuiltinMultiply
    , genTypedBuiltinDivide
    , genTypedBuiltinAddFailure
    , genTypedBuiltinMultiplyFailure
    , genTypedBuiltinConcatenate
    , genTypedBuiltinConcatenateFailure
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

-- TODO: rename me to @TermWith@.
-- | A PLC 'Term' along with the correspoding Haskell value.
data TermOf a = TermOf
    { _termOfTerm  :: Term TyName Name ()  -- ^ The PLC term
    , _termOfValue :: a                    -- ^ The Haskell value.
    } deriving (Functor, Foldable, Traversable)
-- This has an interesting @Apply@ instance (no pun intended).

-- | A function of this type generates values of built-in typed (see 'TypedBuiltin' for
-- the list of such types) and returns it along with the corresponding PLC value.
-- Bounds induced (as per the spec) by the 'Size' values must be met, but can be narrowed.
type TypedBuiltinGenT m = forall a. TypedBuiltin Size a -> GenT m (TermOf a)

-- | 'TypedBuiltinGenT' specified to 'Identity'.
type TypedBuiltinGen = TypedBuiltinGenT Identity

instance (PrettyBy config a, PrettyBy config (Term TyName Name ())) =>
        PrettyBy config (TermOf a) where
    prettyBy config (TermOf t x) = prettyBy config t <+> "~>" <+> prettyBy config x

attachCoercedTerm
    :: (MonadQuote m, PrettyDynamic a) => TypedBuiltin Size a -> GenT m a -> GenT m (TermOf a)
attachCoercedTerm tb genX = do
    x <- genX
    -- Previously we used 'unsafeMakeBuiltin' here, however it didn't allow to generate
    -- terms with out-of-bounds constants. Hence we now use 'makeBuiltinNOCHECK'.
    -- The right thing would be to parameterize this function by a built-in maker,
    -- so we check bounds when this makes sense and do not check otherwise.
    -- But this function is used rather deeply in the pipeline, so we need to
    -- attach a 'ReaderT' to 'm' instead of parameterizing the function and
    -- this just makes everything convoluted. We anyway check bounds down the pipeline.
    term <- liftQuote . makeBuiltinNOCHECK $ TypedBuiltinValue tb x
    return $ TermOf term x

-- | Update a typed built-ins generator by overwriting the generator for a certain built-in.
updateTypedBuiltinGen
    :: (MonadQuote m, PrettyDynamic a)
    => TypedBuiltin Size a  -- ^ A generator of which built-in to overwrite.
    -> GenT m a             -- ^ A new generator.
    -> TypedBuiltinGenT m   -- ^ An old typed built-ins generator.
    -> TypedBuiltinGenT m   -- ^ The updated typed built-ins generator.
updateTypedBuiltinGen tbNew genX genTb tbOld
    | Just Refl <- tbNew `geq` tbOld = attachCoercedTerm tbOld genX
    | otherwise                      = genTb tbOld

-- | Update a sized typed built-ins generator by overwriting the generator for a certain built-in.
updateTypedBuiltinGenSized
    :: (MonadQuote m, PrettyDynamic a)
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
    updateTypedBuiltinGenSized TypedBuiltinSizedInt $
        uncurry genInteger . toInclusiveBoundsInt

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
updateTypedBuiltinGenSize = updateTypedBuiltinGenSized TypedBuiltinSizedSize (\_ -> return ())

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

-- | A default sized built-ins generator that produces values in bounds seen in the spec.
genTypedBuiltinDef :: MonadQuote m => TypedBuiltinGenT m
genTypedBuiltinDef
    = updateTypedBuiltinGenInt
          (\low high -> Gen.integral $ Range.linearFrom 0 low high)
    $ updateTypedBuiltinGenBS
          (genLowerBytes . Range.linear 0)
    $ updateTypedBuiltinGenSize
    $ updateTypedBuiltinGenBool Gen.bool
    $ genTypedBuiltinFail

-- | A sized built-ins generator that produces small values in bounds seen in the spec.
genTypedBuiltinSmall :: MonadQuote m => TypedBuiltinGenT m
genTypedBuiltinSmall
    = updateTypedBuiltinGenInt
          (\low high -> Gen.integral $ Range.constantFrom 0 (iasqrt low `div` 2) (isqrt high `div` 2))
    $ updateTypedBuiltinGenBS
          (genLowerBytes . Range.constant 0 . (`div` 3) . (* 2))
    $ genTypedBuiltinDef

-- | A sized built-ins generator that produces values outside of bounds seen in the spec
-- for @integer@s and @bytestring@s.
genTypedBuiltinOutOfBounds :: MonadQuote m => TypedBuiltinGenT m
genTypedBuiltinOutOfBounds
    = updateTypedBuiltinGenInt
          (\low high -> Gen.choice
                [ Gen.integral $ Range.linear (low - high - 1) (low - 1)
                , Gen.integral $ Range.linear (high + 1) (high - low + 1)
                ])
    $ updateTypedBuiltinGenBS
          (\s -> genLowerBytes $ Range.linear (s + 1) (s * 2 + 1))
    $ genTypedBuiltinDef

-- | A sized built-ins generator that produces 'Integer's in bounds narrowed by a factor of 2,
-- so that one can use '(+)' or '(-)' over such integers without the risk of getting an overflow.
genTypedBuiltinSum :: MonadQuote m => TypedBuiltinGenT m
genTypedBuiltinSum
    = updateTypedBuiltinGenInt
          (\low high -> Gen.integral $ Range.linear (low `div` 2) (high `div` 2))
    $ genTypedBuiltinDef

-- | A sized built-ins generator that produces 'Integer's in bounds narrowed by 'isqrtt',
-- so that one can use '(*)' over such integers without the risk of getting an overflow.
genTypedBuiltinMultiply :: MonadQuote m => TypedBuiltinGenT m
genTypedBuiltinMultiply
    = updateTypedBuiltinGenInt
          (\low high -> Gen.integral $ Range.linear (negate . isqrt . abs $ low) (isqrt high))
    $ genTypedBuiltinDef

-- | A sized built-ins generator that doesn't produce @0 :: Integer@,
-- so that one case use 'div' or 'mod' over such integers without the risk of dividing by zero.
genTypedBuiltinDivide :: MonadQuote m => TypedBuiltinGenT m
genTypedBuiltinDivide
    = updateTypedBuiltinGenInt
          (\low high -> Gen.filter (/= 0) . Gen.integral $ Range.linear low high)
    $ genTypedBuiltinDef

-- | A sized built-ins generator that produces 'Integer's in the @(high `div` 2, high]@ interval,
-- so that one can use '(+)' over such integers and reliably get an overflow.
genTypedBuiltinAddFailure :: MonadQuote m => TypedBuiltinGenT m
genTypedBuiltinAddFailure
    = updateTypedBuiltinGenInt
          (\_ high -> Gen.integral $ Range.linear (high `div` 2 + 1) high)
    $ genTypedBuiltinDef

-- | A sized built-ins generator that produces 'Integer's in the @(isqrt high, high]@ interval,
-- so that one can use '(*)' over such integers and reliably get an overflow.
genTypedBuiltinMultiplyFailure :: MonadQuote m => TypedBuiltinGenT m
genTypedBuiltinMultiplyFailure
    = updateTypedBuiltinGenInt
          (\_ high -> Gen.integral $ Range.linear (isqrt high + 1) (isqrt high))
    $ genTypedBuiltinDef

-- | A sized built-ins generator that produces 'ByteString's of such lengths that
-- one can use '<>' over them without the risk of getting an overflow.
genTypedBuiltinConcatenate :: MonadQuote m => TypedBuiltinGenT m
genTypedBuiltinConcatenate
    = updateTypedBuiltinGenBS
          (\high -> genLowerBytes $ Range.linear 0 (high `div` 2))
    $ genTypedBuiltinDef

-- | A sized built-ins generator that produces 'ByteString's of such lengths that
-- one can use '<>' over them and reliably gen an overflow.
genTypedBuiltinConcatenateFailure :: MonadQuote m => TypedBuiltinGenT m
genTypedBuiltinConcatenateFailure
    = updateTypedBuiltinGenBS
          (\high -> genLowerBytes $ Range.linear (high `div` 2 + 1) high)
    $ genTypedBuiltinDef
