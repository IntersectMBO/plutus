module Foundation.Random.ChaChaDRG
    ( State(..)
    , keySize
    ) where

import           Foundation.Class.Storable (peek)
import           Basement.Imports
import           Basement.Types.OffsetSize
import           Basement.Monad
import           Foundation.Random.Class
import           Foundation.Random.DRG
import qualified Basement.UArray as A
import qualified Basement.UArray.Mutable as A
import           GHC.ST
import qualified Foreign.Marshal.Alloc (alloca)

-- | RNG based on ChaCha core.
--
-- The algorithm is identical to the arc4random found in recent BSDs,
-- namely a ChaCha core provide 64 bytes of random from 32 bytes of
-- key.
newtype State = State (UArray Word8)

instance RandomGen State where
    randomNew = State <$> getRandomBytes keySize
    randomNewFrom bs
        | A.length bs == keySize = Just $ State bs
        | otherwise              = Nothing
    randomGenerate = generate
    randomGenerateWord64 = generateWord64
    randomGenerateF32 = generateF32
    randomGenerateF64 = generateF64

keySize :: CountOf Word8
keySize = 32

generate :: CountOf Word8 -> State -> (UArray Word8, State)
generate n (State key) = runST $ do
    dst    <- A.newPinned n
    newKey <- A.newPinned keySize
    A.withMutablePtr dst        $ \dstP    ->
        A.withMutablePtr newKey $ \newKeyP ->
        A.withPtr key           $ \keyP    -> do
            _ <- unsafePrimFromIO $ c_rngv1_generate newKeyP dstP keyP n
            return ()
    (,) <$> A.unsafeFreeze dst
        <*> (State <$> A.unsafeFreeze newKey)

generateWord64 :: State -> (Word64, State)
generateWord64 (State key) = runST $ unsafePrimFromIO $
    Foreign.Marshal.Alloc.alloca $ \dst -> do
        newKey <- A.newPinned keySize
        A.withMutablePtr newKey $ \newKeyP ->
          A.withPtr key           $ \keyP  ->
            c_rngv1_generate_word64 newKeyP dst keyP *> return ()
        (,) <$> peek dst <*> (State <$> A.unsafeFreeze newKey)

generateF32 :: State -> (Float, State)
generateF32 (State key) = runST $ unsafePrimFromIO $
    Foreign.Marshal.Alloc.alloca $ \dst -> do
        newKey <- A.newPinned keySize
        A.withMutablePtr newKey $ \newKeyP ->
          A.withPtr key           $ \keyP  ->
            c_rngv1_generate_f32 newKeyP dst keyP *> return ()
        (,) <$> peek dst <*> (State <$> A.unsafeFreeze newKey)

generateF64 :: State -> (Double, State)
generateF64 (State key) = runST $ unsafePrimFromIO $
    Foreign.Marshal.Alloc.alloca $ \dst -> do
        newKey <- A.newPinned keySize
        A.withMutablePtr newKey $ \newKeyP ->
          A.withPtr key           $ \keyP  ->
            c_rngv1_generate_f64 newKeyP dst keyP *> return ()
        (,) <$> peek dst <*> (State <$> A.unsafeFreeze newKey)

-- return 0 on success, !0 for failure
foreign import ccall unsafe "foundation_rngV1_generate"
   c_rngv1_generate :: Ptr Word8 -- new key
                    -> Ptr Word8 -- destination
                    -> Ptr Word8 -- current key
                    -> CountOf Word8 -- number of bytes to generate
                    -> IO Word32

foreign import ccall unsafe "foundation_rngV1_generate_word64"
   c_rngv1_generate_word64 :: Ptr Word8  -- new key
                           -> Ptr Word64 -- destination
                           -> Ptr Word8  -- current key
                           -> IO Word32

foreign import ccall unsafe "foundation_rngV1_generate_f32"
   c_rngv1_generate_f32 :: Ptr Word8  -- new key
                        -> Ptr Float -- destination
                        -> Ptr Word8  -- current key
                        -> IO Word32

foreign import ccall unsafe "foundation_rngV1_generate_f64"
   c_rngv1_generate_f64 :: Ptr Word8  -- new key
                        -> Ptr Double -- destination
                        -> Ptr Word8  -- current key
                        -> IO Word32
