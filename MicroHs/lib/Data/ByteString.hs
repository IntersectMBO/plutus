module Data.ByteString(

  ByteString,
  StrictByteString,

  -- * Introducing and eliminating 'ByteString's
  empty, singleton, pack, unpack,
  fromStrict, toStrict,
  fromFilePath, toFilePath,

  -- * Basic interface
  cons, snoc, append, head, uncons, unsnoc,
  last, tail, init,
  null, length,

  -- * Transforming ByteStrings
  map,
  reverse,
  intersperse,
  intercalate,
  transpose,

  -- * Reducing 'ByteString's (folds)
  foldl, foldl', foldl1, foldl1',

  foldr, foldr', foldr1, foldr1',

  -- ** Special folds
  concat,
  concatMap,
  any,
  all,
  maximum,
  minimum,

  -- * Building ByteStrings
  -- ** Scans
  scanl, scanl1, scanr, scanr1,

  -- ** Accumulating maps
  mapAccumL, mapAccumR,

  -- ** Generating and unfolding ByteStrings
  replicate,
  unfoldr,
  unfoldrN,

  -- * Substrings

  -- ** Breaking strings
  take,
  takeEnd,
  drop,
  dropEnd,
  splitAt,
  takeWhile,
  takeWhileEnd,
  dropWhile,
  dropWhileEnd,
  span,
  spanEnd,
  break,
  breakEnd,
  group,
  groupBy,
  inits,
  tails,
  initsNE,
  tailsNE,
  stripPrefix,
  stripSuffix,

  -- ** Breaking into many substrings
  split,
  splitWith,

  -- * Predicates
  isPrefixOf,
  isSuffixOf,
  isInfixOf,

  -- ** Encoding validation
  isValidUtf8,

  -- ** Search for arbitrary substrings
  breakSubstring,

  -- * Searching ByteStrings

  -- ** Searching by equality
  elem,
  notElem,

  -- ** Searching with a predicate
  find,
  filter,
  partition,

  -- * Indexing ByteStrings
  index,
  indexMaybe,
  (!?),
  elemIndex,
  elemIndices,
  elemIndexEnd,
  findIndex,
  findIndices,
  findIndexEnd,
  count,

  -- * Zipping and unzipping ByteStrings
  zip,
  zipWith,
  packZipWith,
  unzip,

  -- * Ordered ByteStrings
  sort,

  -- * Low level conversions
  -- ** Copying ByteStrings
  copy,

  -- ** Packing 'CString's and pointers
  packCString,
  packCStringLen,

  -- ** Using ByteStrings as 'CString's
  useAsCString,
  useAsCStringLen,

  -- * I\/O with 'ByteString's

  -- ** Standard input and output
  getLine,
  getContents,
  putStr,
  interact,

  -- ** Files
  readFile,
  writeFile,
  appendFile,

  -- ** I\/O with Handles
  hGetLine,
  hGetContents,
  hGet,
  hGetSome,
  hGetNonBlocking,
  hPut,
  hPutNonBlocking,
  hPutStr,
  ) where
import Control.Exception (evaluate)
import Data.Bits
import Data.ByteString.Internal
import Data.Function (($!))
import Data.List qualified as P
import Data.List.NonEmpty (NonEmpty, fromList)
import Data.Monoid.Internal
import Data.Semigroup
import Data.String
import Data.Word (Word8)
import Foreign.C.String (CString, CStringLen)
import Foreign.C.Types (CChar)
import Foreign.ForeignPtr
import Foreign.Ptr (Ptr)
import MiniPrelude as P hiding (length, null)
import Prelude qualified ()
import System.IO qualified as P
import System.IO (Handle, IOMode (..), hClose, openFile, stdin, stdout)
import System.IO.Internal (BFILE, withHandleRd, withHandleWr)

foreign import ccall "readb" c_readb :: CString -> Int -> Ptr BFILE -> IO Int
foreign import ccall "writeb" c_writeb :: CString -> Int -> Ptr BFILE -> IO Int

type StrictByteString = ByteString

bsUnimp :: String -> a
bsUnimp s = P.error $ "Data.ByteString." P.++ s P.++ " unimplemented"

-----------------------------------------

fromStrict :: ByteString -> a
fromStrict = bsUnimp "fromStrict"

toStrict :: a -> ByteString
toStrict = bsUnimp "toStrict"

fromFilePath :: FilePath -> IO ByteString
fromFilePath = return . fromString

toFilePath :: ByteString -> IO FilePath
toFilePath = return . toString

infixr 5 `cons` --same as list (:)
infixl 5 `snoc`

cons :: Word8 -> ByteString -> ByteString
cons c bs = append (pack [c]) bs

snoc :: ByteString -> Word8 -> ByteString
snoc bs c = append bs (pack [c])

head :: ByteString -> Word8
head bs
  | null bs = bsError "head: empty"
  | otherwise = primBSindex bs 0

tail :: ByteString -> ByteString
tail bs | sz == 0 = bsError "tail: empty"
        | otherwise = substr bs 1 (sz - 1)
        where sz = length bs

uncons :: ByteString -> Maybe (Word8, ByteString)
uncons bs | null bs = Nothing
          | otherwise = Just (head bs, tail bs)

last :: ByteString -> Word8
last bs
  | null bs = bsError "last: empty"
  | otherwise = primBSindex bs (length bs - 1)

init :: ByteString -> ByteString
init bs | sz == 0 = bsError "init: empty"
        | otherwise = substr bs 0 (sz - 1)
        where sz = length bs

unsnoc :: ByteString -> Maybe (ByteString, Word8)
unsnoc bs | null bs = Nothing
          | otherwise = Just (init bs, last bs)

map :: (Word8 -> Word8) -> ByteString -> ByteString
map f = pack . P.map f . unpack

reverse :: ByteString -> ByteString
reverse = pack . P.reverse . unpack

intersperse :: Word8 -> ByteString -> ByteString
intersperse x = pack . P.intersperse x . unpack

transpose :: [ByteString] -> [ByteString]
transpose = P.map pack . P.transpose . P.map unpack

foldl :: (a -> Word8 -> a) -> a -> ByteString -> a
foldl f z = P.foldl f z . unpack

foldl' :: (a -> Word8 -> a) -> a -> ByteString -> a
foldl' f z = P.foldl' f z . unpack

foldr :: (Word8 -> a -> a) -> a -> ByteString -> a
foldr k z = P.foldr k z . unpack

foldr' :: (Word8 -> a -> a) -> a -> ByteString -> a
foldr' k z = P.foldr' k z . unpack

foldl1 :: (Word8 -> Word8 -> Word8) -> ByteString -> Word8
foldl1 f = P.foldl1 f . unpack

foldl1' :: (Word8 -> Word8 -> Word8) -> ByteString -> Word8
foldl1' f = P.foldl1' f . unpack

foldr1 :: (Word8 -> Word8 -> Word8) -> ByteString -> Word8
foldr1 f = P.foldr1 f . unpack

foldr1' :: (Word8 -> Word8 -> Word8) -> ByteString -> Word8
foldr1' f = P.foldr1' f . unpack

concat :: [ByteString] -> ByteString
concat = P.foldr append empty

concatMap :: (Word8 -> ByteString) -> ByteString -> ByteString
concatMap f = concat . P.map f . unpack

any :: (Word8 -> Bool) -> ByteString -> Bool
any f = P.any f . unpack

all :: (Word8 -> Bool) -> ByteString -> Bool
all f = P.all f . unpack

maximum :: ByteString -> Word8
maximum = P.maximum . unpack

minimum :: ByteString -> Word8
minimum = P.minimum . unpack

mapAccumL :: (acc -> Word8 -> (acc, Word8)) -> acc -> ByteString -> (acc, ByteString)
mapAccumL f acc bs = (acc', pack ws)
  where (acc', ws) = P.mapAccumL f acc (unpack bs)

mapAccumR :: (acc -> Word8 -> (acc, Word8)) -> acc -> ByteString -> (acc, ByteString)
mapAccumR f acc bs = (acc', pack ws)
  where (acc', ws) = P.mapAccumR f acc (unpack bs)

scanl
    :: (Word8 -> Word8 -> Word8)
    -- ^ accumulator -> element -> new accumulator
    -> Word8
    -- ^ starting value of accumulator
    -> ByteString
    -- ^ input of length n
    -> ByteString
    -- ^ output of length n+1
scanl f v = pack . P.scanl f v . unpack

scanl1 :: (Word8 -> Word8 -> Word8) -> ByteString -> ByteString
scanl1 f = pack . P.scanl1 f . unpack

scanr
    :: (Word8 -> Word8 -> Word8)
    -- ^ element -> accumulator -> new accumulator
    -> Word8
    -- ^ starting value of accumulator
    -> ByteString
    -- ^ input of length n
    -> ByteString
    -- ^ output of length n+1
scanr f v = pack . P.scanr f v . unpack

scanr1 :: (Word8 -> Word8 -> Word8) -> ByteString -> ByteString
scanr1 f = pack . P.scanr1 f . unpack

replicate :: Int -> Word8 -> ByteString
replicate = primBSreplicate

unfoldr :: (a -> Maybe (Word8, a)) -> a -> ByteString
unfoldr f = pack . P.unfoldr f

unfoldrN :: Int -> (a -> Maybe (Word8, a)) -> a -> (ByteString, Maybe a)
unfoldrN i f = loop [] i
  where loop ws i x | i <= 0              = (pack (P.reverse ws), Just x)
                    | Just (w, x') <- f x = loop (w:ws) (i-1) x'
                    | otherwise           = (pack (P.reverse ws), Nothing)

take :: Int -> ByteString -> ByteString
take n bs
  | n <= 0    = empty
  | n >= l    = bs
  | otherwise = substr bs 0 n
  where l = length bs

takeEnd :: Int -> ByteString -> ByteString
takeEnd n bs
  | n <= 0    = empty
  | n >= l    = bs
  | otherwise = substr bs (l - n) n
  where l = length bs

drop :: Int -> ByteString -> ByteString
drop n bs
  | n <= 0    = bs
  | n >= l    = empty
  | otherwise = substr bs n (l - n)
  where l = length bs

dropEnd :: Int -> ByteString -> ByteString
dropEnd n bs
  | n <= 0    = bs
  | n >= l    = empty
  | otherwise = substr bs 0 (l - n)
  where l = length bs

splitAt :: Int -> ByteString -> (ByteString, ByteString)
splitAt n bs = (take n bs, drop n bs)

takeWhile :: (Word8 -> Bool) -> ByteString -> ByteString
takeWhile f = pack . P.takeWhile f . unpack

takeWhileEnd :: (Word8 -> Bool) -> ByteString -> ByteString
takeWhileEnd f = pack . P.takeWhileEnd f . unpack

dropWhile :: (Word8 -> Bool) -> ByteString -> ByteString
dropWhile f = pack . P.dropWhile f . unpack

dropWhileEnd :: (Word8 -> Bool) -> ByteString -> ByteString
dropWhileEnd f = pack . P.dropWhileEnd f . unpack

break :: (Word8 -> Bool) -> ByteString -> (ByteString, ByteString)
break p bs = (takeWhile p bs, dropWhile p bs)

breakEnd :: (Word8 -> Bool) -> ByteString -> (ByteString, ByteString)
breakEnd  p bs = (takeWhileEnd p bs, dropWhileEnd p bs)

span :: (Word8 -> Bool) -> ByteString -> (ByteString, ByteString)
span p = break (not . p)

spanEnd :: (Word8 -> Bool) -> ByteString -> (ByteString, ByteString)
spanEnd p = breakEnd (not . p)

splitWith :: (Word8 -> Bool) -> ByteString -> [ByteString]
splitWith w = P.map pack . P.splitWith w . unpack

split :: Word8 -> ByteString -> [ByteString]
split w = splitWith (w ==)

group :: ByteString -> [ByteString]
group = P.map pack . P.group . unpack

groupBy :: (Word8 -> Word8 -> Bool) -> ByteString -> [ByteString]
groupBy q = P.map pack . P.groupBy q . unpack

intercalate :: ByteString -> [ByteString] -> ByteString
intercalate s = pack . P.intercalate (unpack s) . P.map unpack

index :: ByteString -> Int -> Word8
index bs i
  | i < 0          = bsError "index: negative index"
  | i >= length bs = bsError "index: index too large"
  | otherwise      = primBSindex bs i

indexMaybe :: ByteString -> Int -> Maybe Word8
indexMaybe bs i
  | i < 0 || i >= length bs = Nothing
  | otherwise               = Just (primBSindex bs i)

(!?) :: ByteString -> Int -> Maybe Word8
(!?) = indexMaybe

elemIndex :: Word8 -> ByteString -> Maybe Int
elemIndex c = P.elemIndex c . unpack

elemIndexEnd :: Word8 -> ByteString -> Maybe Int
elemIndexEnd c bs = fmap (l -) . P.elemIndex c . P.reverse . unpack $ bs
  where l = length bs - 1

elemIndices :: Word8 -> ByteString -> [Int]
elemIndices w = P.elemIndices w . unpack

count :: Word8 -> ByteString -> Int
count w = P.length . elemIndices w

findIndex :: (Word8 -> Bool) -> ByteString -> Maybe Int
findIndex k = P.findIndex k . unpack

findIndexEnd :: (Word8 -> Bool) -> ByteString -> Maybe Int
findIndexEnd c bs = fmap (l -) . P.findIndex c . P.reverse . unpack $ bs
  where l = length bs - 1

findIndices :: (Word8 -> Bool) -> ByteString -> [Int]
findIndices p = P.findIndices p . unpack

elem :: Word8 -> ByteString -> Bool
elem c ps = case elemIndex c ps of Nothing -> False ; _ -> True

notElem :: Word8 -> ByteString -> Bool
notElem c ps = not (c `elem` ps)

filter :: (Word8 -> Bool) -> ByteString -> ByteString
filter p = pack . P.filter p . unpack

find :: (Word8 -> Bool) -> ByteString -> Maybe Word8
find p = P.find p . unpack

partition :: (Word8 -> Bool) -> ByteString -> (ByteString, ByteString)
partition f bs = (pack a, pack b) where (a, b) = P.partition f (unpack bs)

isPrefixOf :: ByteString -> ByteString -> Bool
isPrefixOf s = P.isPrefixOf (unpack s) . unpack

stripPrefix :: ByteString -> ByteString -> Maybe ByteString
stripPrefix s = fmap pack . P.stripPrefix (unpack s) . unpack

isSuffixOf :: ByteString -> ByteString -> Bool
isSuffixOf a = P.isSuffixOf (unpack a) . unpack

stripSuffix :: ByteString -> ByteString -> Maybe ByteString
stripSuffix s = fmap pack . P.stripSuffix (unpack s) . unpack

isInfixOf :: ByteString -> ByteString -> Bool
isInfixOf a = P.isInfixOf (unpack a) . unpack

isValidUtf8 :: ByteString -> Bool
isValidUtf8 = validUtf8 . unpack
  where
    validUtf8 :: [Word8] -> Bool
    validUtf8 []
      = True
    validUtf8 (x1                : xs) | mask x1 0x80 0x00
      = validUtf8 xs
    validUtf8 (x1 : x2           : xs) | mask x1 0xe0 0xc0 && mask80 x2
      = x1 > 0xc1 && validUtf8 xs
    validUtf8 (x1 : x2 : x3      : xs) | mask x1 0xf0 0xe0 && mask80 x2 && mask80 x3
      = if x1 == 0xe0 then x2 > 0x9f && validUtf8 xs else if x1 == 0xed then x2 < 0xa0 && validUtf8 xs else validUtf8 xs
    validUtf8 (x1 : x2 : x3 : x4 : xs) | mask x1 0xf8 0xf0 && mask80 x2 && mask80 x3 && mask80 x4
      = if x1 == 0xf0 then x2 > 0x8f && validUtf8 xs else if x1 < 0xf4 then validUtf8 xs else x1 == 0xf4 && x2 <= 0x8f && validUtf8 xs
    validUtf8 _
      = False
    mask :: Word8 -> Word8 -> Word8 -> Bool
    mask x m b = x .&. m == b
    mask80 :: Word8 -> Bool
    mask80 x = mask x 0xc0 0x80

breakSubstring :: ByteString -- ^ String to search for
               -> ByteString -- ^ String to search in
               -> (ByteString,ByteString) -- ^ Head and tail of string broken at substring
breakSubstring pat str
  | length pat > length str = (str, empty)
  | otherwise =
    case P.findIndex (P.isPrefixOf (unpack pat)) (P.tails (unpack str)) of
      Nothing -> (str, empty)
      Just i  -> splitAt i str

zip :: ByteString -> ByteString -> [(Word8,Word8)]
zip ps qs = P.zip (unpack ps) (unpack qs)

zipWith :: (Word8 -> Word8 -> a) -> ByteString -> ByteString -> [a]
zipWith f ps qs = P.zipWith f (unpack ps) (unpack qs)

packZipWith :: (Word8 -> Word8 -> Word8) -> ByteString -> ByteString -> ByteString
packZipWith f ps qs = pack $ zipWith f ps qs

unzip :: [(Word8,Word8)] -> (ByteString,ByteString)
unzip ls = (pack (P.map fst ls), pack (P.map snd ls))

inits :: ByteString -> [ByteString]
inits = P.map pack . P.inits . unpack

initsNE :: ByteString -> NonEmpty ByteString
initsNE = fromList . inits

tails :: ByteString -> [ByteString]
tails = P.map pack . P.tails . unpack

tailsNE :: ByteString -> NonEmpty ByteString
tailsNE = fromList . tails

sort :: ByteString -> ByteString
sort = pack . P.sort . unpack

useAsCString :: ByteString -> (CString -> IO a) -> IO a
useAsCString bs act =
  withForeignPtr (primBS2FPtr bs) act

useAsCStringLen :: ByteString -> (CStringLen -> IO a) -> IO a
useAsCStringLen bs act =
  withForeignPtr (primBS2FPtr bs) $ \p -> act (p, length bs)

packCString :: CString -> IO ByteString
packCString = primPackCString

packCStringLen :: CStringLen -> IO ByteString
packCStringLen (cstr, len) = primPackCStringLen cstr len

copy :: ByteString -> ByteString
copy = append empty

getLine :: IO ByteString
getLine = hGetLine stdin

hGetLine :: Handle -> IO ByteString
hGetLine = fmap fromString . P.hGetLine

hPut :: Handle -> ByteString -> IO ()
hPut h bs =
  withHandleWr h $ \bfile ->
    useAsCStringLen bs $ \(cstr, len) ->
      void (c_writeb cstr len bfile)
      -- XXX: flush if not BlockBuffering

hPutNonBlocking :: Handle -> ByteString -> IO ByteString
hPutNonBlocking = bsUnimp "hPutNonBlocking"

hPutStr :: Handle -> ByteString -> IO ()
hPutStr = hPut

putStr :: ByteString -> IO ()
putStr = hPut stdout

hGet :: Handle -> Int -> IO ByteString
hGet h i =
  withHandleRd h $ \bfile -> do
    fp <- mallocForeignPtrBytes i
    bytesRead <- withForeignPtr fp $ \buf -> c_readb buf i bfile
    return $! primFPtr2BS fp bytesRead

hGetNonBlocking :: Handle -> Int -> IO ByteString
hGetNonBlocking h i = bsUnimp "hGetNonBlocking"

hGetSome :: Handle -> Int -> IO ByteString
hGetSome h i = bsUnimp "hGetSome"

hGetContents :: Handle -> IO ByteString
hGetContents h =
  withHandleRd h $ \bfile -> do
    let
      readChunks chunkSize chunks = do
        fp <- mallocForeignPtrBytes chunkSize
        bytesRead <- withForeignPtr fp $ \buf -> c_readb buf chunkSize bfile
        if bytesRead < chunkSize then
          -- EOF
          evaluate $ chunks `append` primFPtr2BS fp bytesRead
        else
          readChunks (chunkSize * 2) (chunks `append` primFPtr2BS fp bytesRead)
    bs <- readChunks 1024 empty
    hClose h
    return bs

getContents :: IO ByteString
getContents = hGetContents stdin

interact :: (ByteString -> ByteString) -> IO ()
interact transformer = getContents >>= putStr . transformer

readFile :: FilePath -> IO ByteString
readFile f = do
  h <- openFile f ReadMode
  hGetContents h

writeFile :: FilePath -> ByteString -> IO ()
writeFile f bs = do
  h <- openFile f WriteMode
  hPut h bs
  hClose h

appendFile :: FilePath -> ByteString -> IO ()
appendFile f bs = do
  h <- openFile f AppendMode
  hPut h bs
  hClose h
