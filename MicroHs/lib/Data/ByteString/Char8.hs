module Data.ByteString.Char8(module Data.ByteString.Char8) where
import qualified Data.ByteString as B
import Data.Coerce
import Data.List.NonEmpty
import Data.Word(Word8)
import Foreign.C.String(CString, CStringLen)
import System.IO(Handle)

newtype ByteString = BS B.ByteString
  deriving (Eq, Ord)

fromFilePath :: FilePath -> IO ByteString
fromFilePath = coerce B.fromFilePath

toFilePath :: ByteString -> IO FilePath
toFilePath = coerce B.toFilePath

cons :: Char -> ByteString -> ByteString
cons = coerce B.cons

snoc :: ByteString -> Char -> ByteString
snoc = coerce B.snoc

head :: ByteString -> Char
head = coerce B.head

tail :: ByteString -> ByteString
tail = coerce B.tail

uncons :: ByteString -> Maybe (Char, ByteString)
uncons = coerce B.uncons

last :: ByteString -> Char
last = coerce B.last

init :: ByteString -> ByteString
init = coerce B.init

unsnoc :: ByteString -> Maybe (ByteString, Char)
unsnoc = coerce B.unsnoc

null :: ByteString -> Bool
null = coerce B.null

map :: (Char -> Char) -> ByteString -> ByteString
map = coerce B.map

reverse :: ByteString -> ByteString
reverse = coerce B.reverse

intersperse :: Char -> ByteString -> ByteString
intersperse = coerce B.intersperse

transpose :: [ByteString] -> [ByteString]
transpose = coerce B.transpose

foldl :: (a -> Char -> a) -> a -> ByteString -> a
foldl f z x = B.foldl (coerce f) z (coerce x)

foldl' :: (a -> Char -> a) -> a -> ByteString -> a
foldl' f z x = B.foldl' (coerce f) z (coerce x)

foldr :: (Char -> a -> a) -> a -> ByteString -> a
foldr f z x = B.foldr (coerce f) z (coerce x)

foldr' :: (Char -> a -> a) -> a -> ByteString -> a
foldr' f z x = B.foldr' (coerce f) z (coerce x)

foldl1 :: (Char -> Char -> Char) -> ByteString -> Char
foldl1 = coerce B.foldl1

foldl1' :: (Char -> Char -> Char) -> ByteString -> Char
foldl1' = coerce B.foldl1'

foldr1 :: (Char -> Char -> Char) -> ByteString -> Char
foldr1 = coerce B.foldr1

foldr1' :: (Char -> Char -> Char) -> ByteString -> Char
foldr1' = coerce B.foldr1'

concat :: [ByteString] -> ByteString
concat = coerce B.concat

concatMap :: (Char -> ByteString) -> ByteString -> ByteString
concatMap = coerce B.concatMap

any :: (Char -> Bool) -> ByteString -> Bool
any = coerce B.any

all :: (Char -> Bool) -> ByteString -> Bool
all = coerce B.all

maximum :: ByteString -> Char
maximum = coerce B.maximum

minimum :: ByteString -> Char
minimum = coerce B.minimum

mapAccumL :: (acc -> Char -> (acc, Char)) -> acc -> ByteString -> (acc, ByteString)
mapAccumL f s x = coerce (B.mapAccumL (coerce f) s (coerce x))

mapAccumR :: (acc -> Char -> (acc, Char)) -> acc -> ByteString -> (acc, ByteString)
mapAccumR f s x = coerce (B.mapAccumR (coerce f) s (coerce x))

scanl1 :: (Char -> Char -> Char) -> ByteString -> ByteString
scanl1 = coerce B.scanl1

scanr1 :: (Char -> Char -> Char) -> ByteString -> ByteString
scanr1 = coerce B.scanr1

replicate :: Int -> Char -> ByteString
replicate = coerce B.replicate

unfoldr :: (a -> Maybe (Char, a)) -> a -> ByteString
unfoldr f a = coerce (B.unfoldr (coerce f) a)

unfoldrN :: Int -> (a -> Maybe (Char, a)) -> a -> (ByteString, Maybe a)
unfoldrN n f a = coerce (B.unfoldrN n (coerce f) a)

take :: Int -> ByteString -> ByteString
take = coerce B.take

takeEnd :: Int -> ByteString -> ByteString
takeEnd = coerce B.takeEnd

drop  :: Int -> ByteString -> ByteString
drop = coerce B.drop

dropEnd :: Int -> ByteString -> ByteString
dropEnd = coerce B.dropEnd

splitAt :: Int -> ByteString -> (ByteString, ByteString)
splitAt = coerce B.splitAt

takeWhile :: (Char -> Bool) -> ByteString -> ByteString
takeWhile = coerce B.takeWhile

takeWhileEnd :: (Char -> Bool) -> ByteString -> ByteString
takeWhileEnd = coerce B.takeWhileEnd

dropWhile :: (Char -> Bool) -> ByteString -> ByteString
dropWhile = coerce B.dropWhile

dropWhileEnd :: (Char -> Bool) -> ByteString -> ByteString
dropWhileEnd = coerce B.dropWhileEnd

break :: (Char -> Bool) -> ByteString -> (ByteString, ByteString)
break = coerce B.break

breakEnd :: (Char -> Bool) -> ByteString -> (ByteString, ByteString)
breakEnd = coerce B.breakEnd

span :: (Char -> Bool) -> ByteString -> (ByteString, ByteString)
span = coerce B.span

spanEnd :: (Char -> Bool) -> ByteString -> (ByteString, ByteString)
spanEnd = coerce B.spanEnd

splitWith :: (Char -> Bool) -> ByteString -> [ByteString]
splitWith = coerce B.splitWith

split :: Char -> ByteString -> [ByteString]
split = coerce B.split

group :: ByteString -> [ByteString]
group = coerce B.group

groupBy :: (Char -> Char -> Bool) -> ByteString -> [ByteString]
groupBy = coerce B.groupBy

intercalate :: ByteString -> [ByteString] -> ByteString
intercalate = coerce B.intercalate

index :: ByteString -> Int -> Char
index = coerce B.index

indexMaybe :: ByteString -> Int -> Maybe Char
indexMaybe = coerce B.indexMaybe

(!?) :: ByteString -> Int -> Maybe Char
(!?) = coerce (B.!?)

elemIndex :: Char -> ByteString -> Maybe Int
elemIndex = coerce B.elemIndex

elemIndexEnd :: Char -> ByteString -> Maybe Int
elemIndexEnd = coerce B.elemIndexEnd

elemIndices :: Char -> ByteString -> [Int]
elemIndices = coerce B.elemIndices

count :: Char -> ByteString -> Int
count = coerce B.count

findIndex :: (Char -> Bool) -> ByteString -> Maybe Int
findIndex = coerce B.findIndex

findIndexEnd :: (Char -> Bool) -> ByteString -> Maybe Int
findIndexEnd = coerce B.findIndexEnd

findIndices :: (Char -> Bool) -> ByteString -> [Int]
findIndices = coerce B.findIndices

elem :: Char -> ByteString -> Bool
elem = coerce B.elem

notElem :: Char -> ByteString -> Bool
notElem = coerce B.notElem

filter :: (Char -> Bool) -> ByteString -> ByteString
filter = coerce B.filter

find :: (Char -> Bool) -> ByteString -> Maybe Char
find = coerce B.find

partition :: (Char -> Bool) -> ByteString -> (ByteString, ByteString)
partition = coerce B.partition

isPrefixOf :: ByteString -> ByteString -> Bool
isPrefixOf = coerce B.isPrefixOf

stripPrefix :: ByteString -> ByteString -> Maybe ByteString
stripPrefix = coerce B.stripPrefix

isSuffixOf :: ByteString -> ByteString -> Bool
isSuffixOf = coerce B.isSuffixOf

stripSuffix :: ByteString -> ByteString -> Maybe ByteString
stripSuffix = coerce B.stripSuffix

isInfixOf :: ByteString -> ByteString -> Bool
isInfixOf = coerce B.isInfixOf

isValidUtf8 :: ByteString -> Bool
isValidUtf8 = coerce B.isValidUtf8

breakSubstring :: ByteString -> ByteString -> (ByteString,ByteString)
breakSubstring = coerce B.breakSubstring

zip :: ByteString -> ByteString -> [(Char,Char)]
zip = coerce B.zip

zipWith :: (Char -> Char -> a) -> ByteString -> ByteString -> [a]
zipWith f x y = B.zipWith (coerce f) (coerce x) (coerce y)

packZipWith :: (Char -> Char -> Char) -> ByteString -> ByteString -> ByteString
packZipWith = coerce B.packZipWith

unzip :: [(Char,Char)] -> (ByteString,ByteString)
unzip = coerce B.unzip

inits :: ByteString -> [ByteString]
inits = coerce B.inits

initsNE :: ByteString -> NonEmpty ByteString
initsNE = coerce B.initsNE

tails :: ByteString -> [ByteString]
tails = coerce B.tails

tailsNE :: ByteString -> NonEmpty ByteString
tailsNE = coerce B.tailsNE

sort :: ByteString -> ByteString
sort = coerce B.sort

useAsCString :: ByteString -> (CString -> IO a) -> IO a
useAsCString x = B.useAsCString (coerce x)

useAsCStringLen :: ByteString -> (CStringLen -> IO a) -> IO a
useAsCStringLen x = B.useAsCStringLen (coerce x)

packCString :: CString -> IO ByteString
packCString = coerce B.packCString

packCStringLen :: CStringLen -> IO ByteString
packCStringLen = coerce B.packCStringLen

copy :: ByteString -> ByteString
copy = coerce B.copy

getLine :: IO ByteString
getLine = coerce B.getLine

hGetLine :: Handle -> IO ByteString
hGetLine = coerce B.hGetLine

hPut :: Handle -> ByteString -> IO ()
hPut = coerce B.hPut

hPutNonBlocking :: Handle -> ByteString -> IO ByteString
hPutNonBlocking = coerce B.hPutNonBlocking

hPutStr :: Handle -> ByteString -> IO ()
hPutStr = coerce B.hPutStr

putStr :: ByteString -> IO ()
putStr = coerce B.putStr

hGet :: Handle -> Int -> IO ByteString
hGet = coerce B.hGet

hGetNonBlocking :: Handle -> Int -> IO ByteString
hGetNonBlocking = coerce B.hGetNonBlocking

hGetSome :: Handle -> Int -> IO ByteString
hGetSome = coerce B.hGetSome

hGetContents :: Handle -> IO ByteString
hGetContents = coerce B.hGetContents

getContents :: IO ByteString
getContents = coerce B.getContents

interact :: (ByteString -> ByteString) -> IO ()
interact = coerce B.interact

readFile :: FilePath -> IO ByteString
readFile = coerce B.readFile

writeFile :: FilePath -> ByteString -> IO ()
writeFile = coerce B.writeFile

appendFile :: FilePath -> ByteString -> IO ()
appendFile = coerce B.appendFile
