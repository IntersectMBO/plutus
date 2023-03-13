{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeFamilies      #-}
module UntypedPlutusCore.Evaluation.Machine.Cek.StepCounter where

import Control.Monad.ST
import Data.Foldable (for_)
import Data.Functor.Identity
import Data.Kind
import Data.Primitive
import Data.Word
import Data.Word64Array.Word8 qualified as WA64

class (Num (Index c), Integral (Index c), Monad (M c)) => StepCounter c where
    type Index c :: Type
    type M c :: Type -> Type
    newCounter :: (M c) c
    resetCounter :: c -> (M c) c
    resetCounter _ = newCounter

    iforCounter :: Applicative f => c -> (Index c -> Word8 -> f ()) -> (M c) (f ())

    readCounter :: c -> Index c -> (M c) Word8
    writeCounter :: c -> Index c -> Word8 -> (M c) c
    overIndex :: Index c -> (Word8 -> Word8) -> c -> (M c) c
    overIndex i f c = do
      v <- readCounter c i
      writeCounter c i (f v)

instance StepCounter WA64.WordArray where
    type Index WA64.WordArray = WA64.Index
    type M WA64.WordArray = Identity

    newCounter = pure $ WA64.WordArray 0
    iforCounter c f = pure $ WA64.iforWordArray c f

    readCounter c i = pure $ WA64.readArray c i
    writeCounter c i v = pure $ WA64.writeArray c i v
    overIndex i f c = pure $ WA64.overIndex i f c

instance StepCounter (MutablePrimArray s Word8) where
    type Index (MutablePrimArray s Word8) = Int
    type M (MutablePrimArray s Word8) = ST s
    newCounter = newPrimArray 8 >>= resetCounter
    resetCounter c = setPrimArray c 0 8 0 >> pure c
    readCounter = readPrimArray
    writeCounter c i v = writePrimArray c i v >> pure c
    iforCounter c f = do
      c' <- unsafeFreezePrimArray c
      pure $ for_ [0..sizeofPrimArray c'] $ \i -> f i (indexPrimArray c' i)
