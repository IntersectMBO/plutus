
{-# LANGUAGE CPP                       #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE ScopedTypeVariables       #-}
module Test.Data.Values where

import Control.DeepSeq
import Control.Exception
import Data.ByteString qualified as B
import Data.ByteString.Lazy qualified as L
import Data.ByteString.Short.Internal qualified as SBS
import Data.Char
import Data.Foldable
import Data.Int
import Data.IntMap qualified as IM
import PlutusCore.Flat
-- import qualified Data.IntSet                    as IS
-- import           Data.List
import Data.Map qualified as M
import Data.Sequence qualified as Seq
import Data.Text qualified as T
import Data.Word
import Test.Data
import Test.Data2 qualified as D2
-- import Data.Array as A


instance NFData Various
instance NFData a => NFData (List a)
instance NFData a => NFData (D2.List a)
instance NFData N
instance NFData a => NFData (ListS a)
instance NFData a => NFData (Stream a)
instance NFData a => NFData (Tree a)
instance NFData Car
instance NFData Engine
instance NFData OptionalExtra
instance NFData CarModel
instance NFData Consumption
instance NFData Acceleration

floatT = ("float",-234.123123::Float)
doubleT = ("double",-1.91237::Double)

a01 = A0 B1 (B0 (C0 (A1 N N D2.Nil2 D2.Nil2))) (D0  E1)

ab0 = A (B (A (BB 'g')))

pe1 :: PerfectF Maybe Bool
pe1 = ConsP True (ConsP (Just False) (ConsP (Just (Just True)) NilP))

pr1 :: Pr Either List Int
pr1 = Pr (Right (C 3 N))
f1,f2,f3:: Free [] Int
f1 = Pure 1
f2 = Roll [Pure 1,Pure 2]
f3 = Roll [Roll [Pure 3],Pure 4]

rr1 :: RR Char () Int8
rr1 = RAB 'a' (RN 11 () 'b') ()

-- h = from Three
infList :: List Bool
infList = C True infList

hl1 = [1,3..111::Word]
hl2 = [1,3..111::Int]
hl3 = [False,True,True,False,True,True,True,True,False,True,True,True,True,False,True,False]

b1 = B.pack [99,173,186,44,187,124,87,186,104,99,138,202,53,137,22,5,44,244,234,7,159,119,22,234]
b2 = B.pack . concat . replicate 100 $ [235,7,135,117,255,69,100,113,113,82,128,181,200,146,155,228,144,65,83,162,130,236,235,7,135,117,255,69,100,113,113,82,128,181,200,146,155,228,144,65,83,162,130,236,235,7,135,117,255,69,100,113,113,82,128,181,200,146,155,228,144,65,83,162,130,236]

lb1 = L.pack . B.unpack $ b1
lb2 = L.fromChunks $ replicate 100 $ B.replicate 400 33

s1 = "a"
s2 = "中文版本"
s3 = ['A'..'z']
s4 :: [Char]
s4 = Prelude.concatMap show [1::Int ..400]

t1 = T.pack s1
t2 = T.pack s2
t3 = T.pack s3
t4 = T.pack s4


p1 :: Phantom Char
p1 = Phantom

--toList N = []
--toList (C h t) = h : (toList t)

l2L []     = N
l2L (x:xs) = C x (l2L xs)

l1 = l2L $ take 11 [11::Word8,22..33]

lBool :: List Bool
lBool = l2L $ map odd [1::Int ..99]

lBool2 :: List Bool
lBool2 = l2L $ map odd [1::Int ..1000]

lBool0 = C False (C True (C True (C False (C False (C False (C True (C False (C True (C False (C True (C True (C False (C False (C False N))))))))))))))

lN0 = C Three (C One N)

lN = C Three (C Three (C One (C One (C Three (C Four (C One (C Five (C Two (C Three (C Four (C Two (C Five (C Five (C Two (C Four (C Three (C One (C Four (C Five (C Two (C Five (C One (C Five (C Two (C One (C One (C Two (C Four N))))))))))))))))))))))))))))

largeSize = 1000000

-- couples :: [(Word32,N)]
couples :: [(Int,N)]
couples = zip [1..] $ ns 1000

lN2 :: List N
lN2 = lnx 1000

lN3 = lnx (largeSize*5)

lnx = l2L . ns

ns n = map asN [1..n]

asN :: Int -> N
asN = toEnum . (`mod` 5)

-- asN = toN . (`mod` 5)

-- toN :: Integer -> N
-- toN 1 = One
-- toN 2 = Two
-- toN 3 = Three
-- toN 4 = Four
-- toN _ = Five

asN3 = toN3 . (`mod` 5)
toN3 :: Integer -> (N,N,N)
toN3 1 = (One,Two,Three)
toN3 2 = (Two,Three,Four)
toN3 3 = (Three,Four,Five)
toN3 4 = (Four,Five,One)
toN3 _ = (Four,Five,Two)

t33T =("Tuple of Tuple",t33)
t33 = asN33 4

asN33 :: Integer -> ((N, N, N), (N, N, N), (N, N, N))
asN33 n = (asN3 n,asN3 (n+1),asN3 (n+2))

treeNLarge :: Tree N
treeNLarge = mkTree asN largeSize

treeNNNLarge :: Tree (N,N,N)
treeNNNLarge = mkTree asN3 largeSize

treeN33Large :: Tree ((N,N,N),(N,N,N),(N,N,N))
treeN33Large = mkTree asN33 largeSize

treeVarious = mkTree (const v2) (100::Int)

mkTreeOf :: forall a. (Enum a ,Bounded a)=> Int -> Tree a
mkTreeOf = let l = fromEnum (maxBound :: a) +1
           in mkTree ((toEnum :: (Int -> a)) . (`mod` l))

mkTree mk = mkTree_ 1
  where
    mkTree_ p 1 = Leaf $ mk p
    mkTree_ p n = let (d,m) = n `divMod` 2
                  in  Node (mkTree_ p d) (mkTree_ (p+d) (d+m))

tree1 :: Tree String
tree1 = Node (Leaf "a leaf") (Node (Leaf "and") (Leaf "more"))

tree2 :: Tree Word64
tree2 = Node (Leaf 17) (Node (Leaf 23) (Leaf 45))

-- ss = take 5 . toList $ stream1

-- stream1 = Stream True stream1

car1 = Car 2343 1965 True ModelB [18,234] "1234" [SunRoof,CruiseControl] (Engine 1200 3 9000 "Fiat" "Petrol") [Consumption 40 18,Consumption 60 23,Consumption 80 25] [(90,[Acceleration 40 12]),(110,[Acceleration 50 11])] "Fiat" "500"

treeN = mkTree asN3 1

longAsciiStrT = ("asciiStr", longS english )

asciiTextT = ("asciiText", T.pack $ longS english )

unicodeTextUTF8T = ("unicodeTextUTF8",UTF8Text unicodeText)

chineseTextUTF8T = ("chineseTextUTF8",UTF8Text chineseText)

#if ! defined (ETA_VERSION)
unicodeTextUTF16T = ("unicodeTextUTF16",UTF16Text unicodeText)
chineseTextUTF16T = ("chineseTextUTF16",UTF16Text chineseText)
#endif

-- chineseTextT = ("chineseText",chinesText)
chineseText = T.pack $ longS chinese


unicodeTextT = ("unicodeText",unicodeText)
unicodeText = T.pack unicodeStr

unicodeStrT = ("unicodeStr",unicodeStr)

unicodeStr = notLongS uniSS


-- uniSS = "\x1F600\&\x1F600\&\x1F600\&I promessi sposi è un celebre romanzo storico di Alessandro Manzoni, ritenuto il più famoso e il più letto tra quelli scritti in lingua italiana[1].维护和平正义 开创美好未来——习近平主席在纪念中国人民抗日战争暨世界反法西斯战争胜利70周年大会上重要讲话在国际社会引起热烈反响"
uniSS = concat [special,latin,chinese]
special = "&forall;\&"
-- Crashes eta
-- emoji = "\x1F600"

english = "To hike, or not to hike? US Federal Reserve chair Janet Yellen faces a tricky decision at today's FOMC meeting. Photograph: Action Press/Rex. Theme park operator Merlin Entertainments suffered a significant drop in visitor numbers to its Alton Towers attraction after a serious rollercoaster accident in June."
latin = "I promessi sposi è un celebre romanzo storico di Alessandro Manzoni, ritenuto il più famoso e il più letto tra quelli scritti in lingua italiana[1]."
chinese = "维护和平正义 开创美好未来——习近平主席在纪念中国人民抗日战争暨世界反法西斯战争胜利70周年大会上重要讲话在国际社会引起热烈反响"

longS =  take 1000000 . concat . repeat

notLongS =  take 1000 . concat . repeat

longBoolListT = ("Long [Bool]",map (odd . ord) (longS uniSS) :: [Bool])

arr0 = ("[Bool]",map (odd . ord) unicodeStr :: [Bool])

arr1 = ("[Word]",map (fromIntegral . ord) unicodeStr :: [Word])

arr2 = ("ByteString from String",B.pack . map (fromIntegral . ord) $ unicodeStr)
sbs = ("StrictByteString",b2)
lbs = ("LazyByteString",lb2)
shortbs = ("ShortByteString",SBS.toShort b2)

-- array package
-- arrayT = ("Array",


intMapT = ("IntMap",intMap)
mapT = ("map",dataMap)
mapListT = ("mapList",listMap)
intMap = IM.fromList couples
dataMap = M.fromList couples
listMap = couples

lN2T = ("List N",lN2)
lN3T = ("Large List N",lN3)
nativeListT = ("Large [N]",nativeList)
nativeList = toList lN3
seqNT = ("Seq N",Seq.fromList . toList $ lN2) -- nativeList)
treeNT = ("treeN",treeN)
treeNLargeT = ("treeNLarge",treeNLarge)
treeNNNLargeT = ("treeNNNLarge",treeNNNLarge)
treeN33LargeT = ("treeN33Large",treeN33Large)
treeVariousT = ("Tree Various",treeVarious)
tuple0T = ("block-tuple",(False,(),(3::Word64,33::Word,(True,(),False))))
tupleT = ("tuple",(Two,One,(Five,Three,(Three,(),Two))))
tupleBools = ("tupleBools",(False,(True,False),((True,False,True),(True,False,True))))
oneT   = ("One",One)
tupleWords = ("tupleWord",(18::Word,623723::Word,(8888::Word,823::Word)))
word8T   = ("Word8",34::Word8)
word64T   = ("Word64",34723823923::Word64)
carT = ("car",car1)
wordsT = ("words",wordsV)
wordsV = (18::Word,33::Word8,1230::Word16,9990::Word32,1231232::Word64)
words0T = ("words0",words0V)
words0V = (0::Word,0::Word8,0::Word16,0::Word32,0::Word64)
intsT = ("ints",(444::Int,123::Int8,-8999::Int16,-123823::Int32,-34723823923::Int64))
floatsT = ("floats",floats)
floatsUnaT = ("floats unaligned",(Three,floats))
floats = (3.43::Float,44.23E+23::Double,0.1::Double)
int8T   = ("Int8",-34::Int8)
int64T   = ("Int64",-34723823923::Int64)
integerT   = ("Integer",-3472382392399239230123123::Integer)
charT = ("Char",'a')
unicharT = ("Unicode char", '世')
v1T = ("V1",v1)
v1 = V1 (Just False)
v2T = ("V2",v2)
--v2 = V2 True (Right Nothing) (One,Two,Three)
v2 = V2 True (Right Nothing)
vfT = ("v floats",VF 3.43 44.23E+23 0.1)
vwT = ("v words",vw)
vw = VW 18 33 1230 9990 1231232
-- vw = VW 0 0 0 0 0
viT = ("v ints",VI 444 123 (-8999) (-123823) (-34723823923))
viiT = ("v integers",VII 444 8888 (-34723823923))

-- Copied from binary-typed-0.3/benchmark/Criterion.hs
-- | Data with a normal form.
data NF = forall a. NFData a => NF a

-- | Evaluate 'NF' data to normal form.
force' :: NF -> ()
force' (NF x) = x `deepseq` ()

forceCafs :: IO ()
forceCafs = mapM_ (evaluate . force') cafs

-- | List of all data that should be fully evaluated before a benchmark is
--   run.
cafs :: [NF]
cafs = [
         NF carT
       , NF charT
       , NF unicharT
       , NF wordsT
       , NF words0T
       , NF intsT
       , NF floatT
       , NF doubleT
       , NF floatsT
       , NF floatsUnaT
       , NF tupleT
       , NF tuple0T
       , NF treeNLargeT
       , NF treeNNNLargeT
       , NF treeN33LargeT
       , NF treeNT
       , NF lN2T
       , NF lN3T
       , NF mapT
       , NF mapListT
       , NF nativeListT
       , NF seqNT
       , NF arr1
       , NF arr0
       , NF longS
       , NF unicodeStr
       , NF longBoolListT
       , NF longAsciiStrT
       , NF asciiTextT
       , NF unicodeStrT
       , NF unicodeTextT
       --, NF unicodeTextUTF8T
       --, NF unicodeTextUTF16T
       , NF couples
       , NF v1T
       , NF v2T
       , NF vfT
       , NF vwT
       , NF viT
       , NF viiT
       , NF treeVariousT
       , NF sbs
       , NF lbs
       , NF shortbs
      ]
