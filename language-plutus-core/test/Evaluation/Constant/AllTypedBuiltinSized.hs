-- | This module defines the 'AllTypedBuiltinSized' type and functions of this type
-- which control size-induced bounds of values generated in the 'prop_applyBuiltinName'
-- function and its derivatives defined in the "Apply" module.

{-# LANGUAGE RankNTypes   #-}
{-# LANGUAGE TypeFamilies #-}
module Evaluation.Constant.AllTypedBuiltinSized
    ( AllTypedBuiltinSized
    , TheAllTypedBuiltinSized(..)
    , updateAllTypedBuiltinSized
    , allTypedBuiltinSizedDef
    , allTypedBuiltinSizedSum
    , allTypedBuiltinSizedDiv
    ) where

import           Language.PlutusCore.Constant

import qualified Data.ByteString      as BS
import qualified Data.ByteString.Lazy as BSL
import           Hedgehog hiding (Size, Var, annotate)
import qualified Hedgehog.Gen   as Gen
import qualified Hedgehog.Range as Range

-- | A function of this type generates values of sized builtin types
-- (see 'TypedBuiltinSized' for the list of such types).
-- Bounds induced by the 'Size' parameter (as per the spec) must be met, but can be narrowed.
type AllTypedBuiltinSized = forall m a. Monad m => Size -> TypedBuiltinSized a -> PropertyT m a
-- Note that while this is just a generator, it can't return a @Gen a@, because
-- then we would need to apply 'forAll' to a generated value of abstract type @a@
-- which would force us to constrain @a@ to have a 'Show' instance which is really
-- inconvenient, because we would need to hardcode that constrain into the
-- 'TypeSchemeBuiltin' constructor or do something even sillier.
-- It is likely to be a deferred problem, but maybe we will never need to solve it.

newtype TheAllTypedBuiltinSized = TheAllTypedBuiltinSized
    { unTheAlltypedBuilinSized :: AllTypedBuiltinSized
    }

-- | A sized builtins generator defined only over 'Size' singletons.
-- Fails if asked to generate anything else.
allTypedBuiltinSizedSize :: AllTypedBuiltinSized
allTypedBuiltinSizedSize size TypedBuiltinSizedSize = return size
allTypedBuiltinSizedSize _    tbs                   = fail $ concat
    [ "The generator for the following builtin is not implemented: "
    , show $ eraseTypedBuiltinSized tbs
    ]

class UpdateAllTypedBuiltinSized a where
    type GenUpdater a

    -- | Update a sized builtins generator by changing the generator for a particular @a@.
    updateAllTypedBuiltinSized
        :: TypedBuiltinSized a   -- ^ Used as a @proxy@.
        -> GenUpdater a          -- ^ A function that returns a new generator.
        -> AllTypedBuiltinSized  -- ^ An old sized builtins generator.
        -> AllTypedBuiltinSized  -- ^ The new sized builtint generator.

instance UpdateAllTypedBuiltinSized Integer where
    type GenUpdater Integer = Integer -> Integer -> Gen Integer

    updateAllTypedBuiltinSized _ genInteger _      size TypedBuiltinSizedInt =
        let (low, high) = toBoundsInt size in
            forAll $ genInteger low (high - 1)
    updateAllTypedBuiltinSized _ _          allTbs size tbs                  =
        allTbs size tbs

instance UpdateAllTypedBuiltinSized BSL.ByteString where
    type GenUpdater BSL.ByteString = Int -> Gen BS.ByteString

    updateAllTypedBuiltinSized _ genBytes _      size TypedBuiltinSizedBS =
        forAll . fmap BSL.fromStrict . genBytes $ fromIntegral size
    updateAllTypedBuiltinSized _ _        allTbs size tbs                 =
        allTbs size tbs

-- | A default sized builtins generator that produces values in bounds seen in the spec.
allTypedBuiltinSizedDef :: AllTypedBuiltinSized
allTypedBuiltinSizedDef
    = updateAllTypedBuiltinSized TypedBuiltinSizedInt
          (\low high -> Gen.integral $ Range.linear low high)
    $ updateAllTypedBuiltinSized TypedBuiltinSizedBS
          (Gen.bytes . Range.linear 0)
    $ allTypedBuiltinSizedSize

-- | A sized builtins generator that produces 'Integer's in bounds narrowed by a factor of 2,
-- so one can use '(+)' or '(-)' over such integers without the risk of getting an overflow.
allTypedBuiltinSizedSum :: AllTypedBuiltinSized
allTypedBuiltinSizedSum
    = updateAllTypedBuiltinSized TypedBuiltinSizedInt
          (\low high -> Gen.integral $ Range.linear (low `div` 2) (high `div` 2))
    $ allTypedBuiltinSizedDef

-- | A sized builtins generator that doesn't produce @0 :: Integer@,
-- so one case use 'div' or 'mod' over such integers without the risk of dividing by zero.
allTypedBuiltinSizedDiv :: AllTypedBuiltinSized
allTypedBuiltinSizedDiv
    = updateAllTypedBuiltinSized TypedBuiltinSizedInt
          (\low high -> Gen.filter (/= 0) . Gen.integral $ Range.linear low high)
    $ allTypedBuiltinSizedDef
