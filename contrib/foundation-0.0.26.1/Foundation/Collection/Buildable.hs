-- |
-- Module      : Foundation.Collection.Buildable
-- License     : BSD-style
-- Maintainer  : foundation
-- Stability   : experimental
-- Portability : portable
--
-- An interface for collections that can be built incrementally.
--
module Foundation.Collection.Buildable
    ( Buildable(..)
    , Builder(..)
    , BuildingState(..)
    , builderLift
    , build_
    ) where

import           Basement.UArray
import           Basement.UArray.Mutable
import qualified Basement.BoxedArray as BA
import qualified Basement.String as S
import           Foundation.Collection.Element
import           Basement.Compat.Base
import           Basement.Monad
import           Basement.MutableBuilder
import           Basement.Compat.MonadTrans

-- $setup
-- >>> import Control.Monad.ST
-- >>> import Basement.UArray
-- >>> import Basement.Compat.Base
-- >>> import Basement.OffsetSize

-- | Collections that can be built chunk by chunk.
--
-- Use the 'Monad' instance of 'Builder' to chain 'append' operations
-- and feed it into `build`:
--
-- >>> runST $ build 32 (append 'a' >> append 'b' >> append 'c') :: UArray Char
-- "abc"
class Buildable col where
    {-# MINIMAL append, build #-}

    -- | Mutable collection type used for incrementally writing chunks.
    type Mutable col :: * -> *

    -- | Unit of the smallest step possible in an `append` operation.
    --
    -- A UTF-8 character can have a size between 1 and 4 bytes, so this
    -- should be defined as 1 byte for collections of `Char`.
    type Step col

    append :: (PrimMonad prim) => Element col -> Builder col (Mutable col) (Step col) prim err ()

    build :: (PrimMonad prim)
          => Int -- ^ CountOf of a chunk
          -> Builder col (Mutable col) (Step col) prim err ()
          -> prim (Either err col)

builderLift :: (Buildable c, PrimMonad prim)
            => prim a
            -> Builder c (Mutable c) (Step c) prim err a
builderLift f = Builder $ State $ \(i, st, e) -> do
    ret <- f
    return (ret, (i, st, e))

build_ :: (Buildable c, PrimMonad prim)
       => Int -- ^ CountOf of a chunk
       -> Builder c (Mutable c) (Step c) prim () ()
       -> prim c
build_ sizeChunksI ab = either (\() -> internalError "impossible output") id <$> build sizeChunksI ab

instance PrimType ty => Buildable (UArray ty) where
    type Mutable (UArray ty) = MUArray ty
    type Step (UArray ty) = ty
    append = builderAppend
    {-# INLINE append #-}
    build = builderBuild
    {-# INLINE build #-}

instance Buildable (BA.Array ty) where
    type Mutable (BA.Array ty) = BA.MArray ty
    type Step (BA.Array ty) = ty

    append = BA.builderAppend
    {-# INLINE append #-}
    build = BA.builderBuild
    {-# INLINE build #-}

instance Buildable S.String where
    type Mutable S.String = S.MutableString
    type Step S.String = Word8

    append = S.builderAppend
    {-# INLINE append #-}
    build = S.builderBuild
    {-# INLINE build #-}
