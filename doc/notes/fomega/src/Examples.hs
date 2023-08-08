-- editorconfig-checker-disable-file
{-# LANGUAGE GADTs       #-}
{-# LANGUAGE QuasiQuotes #-}
module Examples where

import AlgTypes
import Large
import Scott
import Solver

import Control.Applicative
import Control.Monad
import System.IO
import System.Random
import Test.QuickCheck

-- (use the runExample :: AlgSignature -> IO () from AlgTypes)

translate :: AlgSignature -> FSignature
translate = scottSig . demutualize

runExample :: AlgSignature -> IO ()
runExample sig = (putStrLn ("before: size = " ++ (show (size sig))))  >>
                 (prettySignature sig) >>
                 (putStrLn "----------") >>
                 (putStrLn ("after: size = " ++ (show (size (demutualize sig))))) >>
                 (prettySignature (demutualize sig))

onlySizes :: AlgSignature -> IO ()
onlySizes sig = (putStrLn ("before: size = " ++ (show (size sig)))) >>
                (putStrLn ("after:  size = " ++ (show (size (demutualize sig)))))

beforeAfter :: AlgSignature -> (Integer,Integer)
beforeAfter sig = (size sig , size (demutualize sig))

-- 'randomTest p size n' generates n random systems of mutually recursive types where each bit is 1 with
-- probability p of size 'size', and returns the size of each system before and after demutualization.
randomTest :: Probability -> Int -> Int -> IO TestResult
randomTest p size n = randomTest' p size n >>= (return . TR p size)

  where
  randomTest' :: Probability -> Int -> Int -> IO [(Integer,Integer)]
  randomTest' p size 0 = return []
  randomTest' p size n = do
    dens <- generate (randomDensity p size)
    let sig = instantiate dens
    rest <- randomTest' p size (pred n)
    return ((beforeAfter sig) : rest)

data TestResult where
  TR :: Probability -> Int -> [(Integer,Integer)] -> TestResult

instance Show TestResult where
  show (TR p size rs) = "number of types: " ++ (show size) ++ "\n" ++
                        "density: " ++ (show p) ++ "\n" ++
                        "number of tests: " ++ (show (length rs)) ++ "\n" ++
                        "results: " ++ "(size before , size after)" ++ "\n" ++
                        let longshow []     = ""
                            longshow (x:xs) = (show x) ++ "\n" ++ longshow xs in
                          (longshow rs)

-- TODAY:
-- + get test data: run a bunch of tests for each density, each number of types in system
-- + plot test data for each density (as points): x-axis is number of types in system, y-axis is demutualized size
--   also plot a line running through the average size across all tests for each number of types.
-- + make images. Be sure to label. Stare at images to draw conclusions.

-- 'testRandom rng t d path' generates t random systems of i types with density d, for each i in rng.
--  It then writes the resulting pairs of (initial size, size after mutual recursion removed) to a
--  file "path" in the current directory.
testRandom :: [Int] -> Int -> Probability -> FilePath -> IO ()
testRandom rng t d path = join (writeResults path <$> mapM (\i -> randomTest d i t) rng)

-- 'testFixed f rng path' computes the (before, after) data for (f i), each i in rng.
testFixed :: (Int -> Density) -> [Int] -> FilePath -> IO ()
testFixed dgen rng path = writeDat path (map (\i -> beforeAfter (instantiate (dgen i))) rng)

writeResults :: FilePath -> [TestResult] -> IO ()
writeResults path rs = writeDat path (concatResults rs)

concatResults :: [TestResult] -> [(Integer,Integer)]
concatResults = foldr (\(TR _ _ p) ps -> p ++ ps) []

-- 'writeDat "name" points' creates / overwrites a file "name" containing the list of points
-- stored in gnuplot's .dat format.
writeDat :: FilePath -> [(Integer,Integer)] -> IO ()
writeDat path points = do
  file <- openFile path WriteMode
  mapM_ (writePoint file) points
  hClose file

writePoint :: Handle -> (Integer,Integer) -> IO ()
writePoint file (x,y) = hPutStrLn file ((show x) ++ " " ++ (show y))
--------------
-- Examples --
--------------
-- parser has a bunch of shift/reduce conflicts, so these might not actually be the thing I was intending due to lack
-- of brackets. Luckily, the demutualizer only requires substitution, so it works anyway.

list :: Decl AlgType
list = algDecl [declExp| list = all x . 1 + (list x) * x |]

binarytree :: Decl AlgType
binarytree = algDecl [declExp| binarytree = all a . 1 + (binaryTree a) * a * (binaryTree a)|]

rosetree :: Decl AlgType
rosetree = algDecl [declExp| rosetree = all a . 1 * (list (rosetree a)) |]

tree :: Decl AlgType
tree = algDecl [declExp| tree = all a . 1 + (a * (forest a)) |]

forest :: Decl AlgType
forest = algDecl [declExp| forest = all a . 1 + ((tree a) * (forest a)) |]

typeF :: Decl AlgType
typeF = algDecl [declExp| f = (all a . 1 + ((f a) * (h a)))|]

typeG :: Decl AlgType
typeG = algDecl [declExp| g = (all a . ((h a) * (g a)) + 1)|]

typeH :: Decl AlgType
typeH = algDecl [declExp| h = (all a . (f a) * (g a))|]

treeForest :: AlgSignature
treeForest = algSignature [tree,forest]

fgh :: AlgSignature
fgh = algSignature [typeF,typeG,typeH]

onlyList :: AlgSignature
onlyList = algSignature [list]

multi :: AlgSignature
multi = algSignature [typeF,typeG,typeH,tree,forest,binarytree,list,rosetree]


-------------------------
-- Generating Examples --
-------------------------

{- We may think of a system of fixed point equations (corresponding to some mutually recursive types)

t1 = T1(t1,...,tn)
...
tn = Tn(t1,...,tn)

in terms of a "density matrix"

t1,1 t1,2 ... t1,n
t2,1 t2,2 ... t2,n
...
tn,1 tn,2 ... tn,n

where ti,j \in Nat is the number of times tj appears in Ti(t1,...,tn).

We can generate a system of mutually recursive types with any given density matrix.

Useful for testing!
-}

type Density = [[Int]] -- really "nxn matrices of Nats". use responsibly

instantiate :: Density -> AlgSignature
instantiate rows = algSignature $
                  map (\(i,t) -> Decl ("t" ++ (show i)) t)
                      (zip [1..] (map (simplify . (instantiateOne 1)) rows))
  where
  instantiateOne :: Int -> [Int] -> AlgType
  instantiateOne i []     = Zero
  instantiateOne i (n:ns) = Sum (n `times` i) (instantiateOne (succ i) ns)
  times :: Int -> Int -> AlgType
  times 0 i = One
  times k i = Prod (Var ("t" ++ (show i))) (times (pred k) i)

-- I don't think we need to be too worried about density matrices with
-- entries that aren't all 0 or 1.

-- in which the nxn matrix is composed entirely of '1's.
veryDense :: Int -> Density
veryDense x = (replicate x (replicate x 1))

-- in which each type definition refers only to itself. (so, not properly mutually recursive)
diagonal :: Int -> Density
diagonal n = count 0 n
  where
  count x n = if x == n then []
                else ((replicate x 0) ++ (1 : (replicate (n - (succ x)) 0))) : (count (succ x) n)

-- in which each definition refers only to the next definition, ensuring that all definitions rely on each other.
thinCycle :: Int -> Density
thinCycle n = map shift (diagonal n)
  where
  shift xs = (last xs) : (init xs)

type Probability = Int -- between 0 and 100 (inclusive)

-- 'randomBit p' is 1 with probability p, 0 with probability (p-1)
randomBit :: Probability -> Gen Int
randomBit p = frequency [(p,elements [1])
                        ,((100-p), elements [0])]

-- 'randomDensity p n' is an nxn matrix of (randomBit p).
randomDensity :: Probability -> Int -> Gen [[Int]]
randomDensity p n = vectorOf n (vectorOf n (randomBit p))

