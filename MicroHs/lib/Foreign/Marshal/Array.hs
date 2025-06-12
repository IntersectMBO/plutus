module Foreign.Marshal.Array(module Foreign.Marshal.Array) where
import qualified Prelude(); import MiniPrelude
import Foreign.Ptr
import Foreign.Storable
import Foreign.Marshal.Alloc

mallocArray :: forall a . Storable a => Int -> IO (Ptr a)
mallocArray size = mallocBytes (size * sizeOf (undefined :: a))

mallocArray0 :: forall a . Storable a => Int -> IO (Ptr a)
mallocArray0 size  = mallocArray (size + 1)

callocArray :: forall a . Storable a => Int -> IO (Ptr a)
callocArray size = callocBytes (size * sizeOf (undefined :: a))

callocArray0 :: forall a . Storable a => Int -> IO (Ptr a)
callocArray0 size  = callocArray (size + 1)

peekArray :: forall a . Storable a => Int -> Ptr a -> IO [a]
peekArray size ptr | size <= 0 = return []
                   | otherwise = f (size-1) []
  where
    f n acc | n < 0 = return acc
    f n acc = do e <- peekElemOff ptr n; f (n-1) (e:acc)

peekArray0 :: forall a . (Storable a, Eq a) => a -> Ptr a -> IO [a]
peekArray0 marker ptr  = do
  size <- lengthArray0 marker ptr
  peekArray size ptr

pokeArray :: forall a . Storable a => Ptr a -> [a] -> IO ()
pokeArray ptr vals0 = go vals0 0
  where go [] _         = return ()
        go (val:vals) n = do { pokeElemOff ptr n val; go vals (n + 1) }

pokeArray0 :: forall a . Storable a => a -> Ptr a -> [a] -> IO ()
pokeArray0 marker ptr vals0 = go vals0 0
  where go []         n = pokeElemOff ptr n marker
        go (val:vals) n = do { pokeElemOff ptr n val; go vals (n + 1) }

newArray :: forall a . Storable a => [a] -> IO (Ptr a)
newArray vals  = do
  ptr <- mallocArray (length vals)
  pokeArray ptr vals
  return ptr

newArray0 :: forall a . Storable a => a -> [a] -> IO (Ptr a)
newArray0 marker vals  = do
  ptr <- mallocArray0 (length vals)
  pokeArray0 marker ptr vals
  return ptr

lengthArray0 :: forall a . (Storable a, Eq a) => a -> Ptr a -> IO Int
lengthArray0 marker ptr = loop 0
  where
    loop i = do
        val <- peekElemOff ptr i
        if val == marker then return i else loop (i+1)

withArrray :: forall a b . Storable a => [a] -> (Ptr a -> IO b) -> IO b
withArrray vals iob = do
  ptr <- newArray vals
  b <- iob ptr
  free ptr
  return b
