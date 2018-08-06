-- | This module defines the 'GenTypedBuiltinSized' type and functions of this type
-- which control size-induced bounds of values generated in the 'prop_applyBuiltinName'
-- function and its derivatives defined in the "Apply" module.

{-# LANGUAGE RankNTypes   #-}
{-# LANGUAGE TypeFamilies #-}
module Evaluation.Constant.GenTypedBuiltinSized
    ( GenTypedBuiltinSized
    , TheGenTypedBuiltinSized(..)
    , updateGenTypedBuiltinSized
    , genTypedBuiltinSizedDef
    , genTypedBuiltinSizedSum
    , genTypedBuiltinSizedDiv
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
type GenTypedBuiltinSized = forall a. Size -> TypedBuiltinSized a -> Gen a

newtype TheGenTypedBuiltinSized = TheGenTypedBuiltinSized
    { unTheAlltypedBuilinSized :: GenTypedBuiltinSized
    }

-- | A sized builtins generator defined only over 'Size' singletons.
-- Fails if asked to generate anything else.
genTypedBuiltinSizedSize :: GenTypedBuiltinSized
genTypedBuiltinSizedSize size TypedBuiltinSizedSize = return size
genTypedBuiltinSizedSize _    tbs                   = fail $ concat
    [ "The generator for the following builtin is not implemented: "
    , show $ eraseTypedBuiltinSized tbs
    ]

class UpdateGenTypedBuiltinSized a where
    type GenUpdater a

    -- | Update a sized builtins generator by changing the generator for a particular @a@.
    updateGenTypedBuiltinSized
        :: TypedBuiltinSized a   -- ^ Used as a @proxy@.
        -> GenUpdater a          -- ^ A function that returns a new generator.
        -> GenTypedBuiltinSized  -- ^ An old sized builtins generator.
        -> GenTypedBuiltinSized  -- ^ The new sized builtint generator.

instance UpdateGenTypedBuiltinSized Integer where
    type GenUpdater Integer = Integer -> Integer -> Gen Integer

    updateGenTypedBuiltinSized _ genInteger _      size TypedBuiltinSizedInt =
        let (low, high) = toBoundsInt size in genInteger low (high - 1)
    updateGenTypedBuiltinSized _ _          allTbs size tbs                  =
        allTbs size tbs

instance UpdateGenTypedBuiltinSized BSL.ByteString where
    type GenUpdater BSL.ByteString = Int -> Gen BS.ByteString

    updateGenTypedBuiltinSized _ genBytes _      size TypedBuiltinSizedBS =
        -- TODO: 'genBytes' might be inappropriate.
        fmap BSL.fromStrict . genBytes $ fromIntegral size
    updateGenTypedBuiltinSized _ _        allTbs size tbs                 =
        allTbs size tbs

-- | A default sized builtins generator that produces values in bounds seen in the spec.
genTypedBuiltinSizedDef :: GenTypedBuiltinSized
genTypedBuiltinSizedDef
    = updateGenTypedBuiltinSized TypedBuiltinSizedInt
          (\low high -> Gen.integral $ Range.linear low high)
    $ updateGenTypedBuiltinSized TypedBuiltinSizedBS
          (Gen.bytes . Range.linear 0)
    $ genTypedBuiltinSizedSize

-- | A sized builtins generator that produces 'Integer's in bounds narrowed by a factor of 2,
-- so one can use '(+)' or '(-)' over such integers without the risk of getting an overflow.
genTypedBuiltinSizedSum :: GenTypedBuiltinSized
genTypedBuiltinSizedSum
    = updateGenTypedBuiltinSized TypedBuiltinSizedInt
          (\low high -> Gen.integral $ Range.linear (low `div` 2) (high `div` 2))
    $ genTypedBuiltinSizedDef

-- | A sized builtins generator that doesn't produce @0 :: Integer@,
-- so one case use 'div' or 'mod' over such integers without the risk of dividing by zero.
genTypedBuiltinSizedDiv :: GenTypedBuiltinSized
genTypedBuiltinSizedDiv
    = updateGenTypedBuiltinSized TypedBuiltinSizedInt
          (\low high -> Gen.filter (/= 0) . Gen.integral $ Range.linear low high)
    $ genTypedBuiltinSizedDef
