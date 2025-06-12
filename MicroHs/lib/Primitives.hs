-- Copyright 2023 Lennart Augustsson
-- See LICENSE file for full license.
module Primitives(module Primitives) where
import qualified Prelude()              -- do not import Prelude
import Data.Bool_Type
--import Data.List_Type
import Data.Ordering_Type

-- These fixities are hardwired
-- infixr -1 ->
-- infixr -2 =>
infix   4 ~

-- Kinds
data Constraint
data Nat
data Symbol
data Type

-- Classes
-- Type equality as a constraint.
type (~) :: forall k . k -> k -> Constraint
class a ~ b | a -> b, b -> a
-- class KnownNat in Data.TypeLits
-- class KnownSymbol in Data.TypeLits

-- Types
data AnyType
--data Char
newtype Char = Char Word
data Int
data FloatW
data IO a
data Word
data Ptr a
data ForeignPtr a
data FunPtr a
data IOArray a
data ThreadId
data MVar a
-- (), (,), (,,), etc are built in to the compiler

primIntAdd :: Int -> Int -> Int
primIntAdd  = _primitive "+"
primIntSub :: Int -> Int -> Int
primIntSub  = _primitive "-"
primIntMul :: Int -> Int -> Int
primIntMul  = _primitive "*"
primIntQuot :: Int -> Int -> Int
primIntQuot = _primitive "quot"
primIntRem :: Int -> Int -> Int
primIntRem  = _primitive "rem"
primIntSubR :: Int -> Int -> Int
primIntSubR = _primitive "subtract"
primIntNeg :: Int -> Int
primIntNeg = _primitive "neg"

primIntEQ   :: Int -> Int -> Bool
primIntEQ   = _primitive "=="
primIntNE   :: Int -> Int -> Bool
primIntNE   = _primitive "/="
primIntLT   :: Int -> Int -> Bool
primIntLT   = _primitive "<"
primIntLE   :: Int -> Int -> Bool
primIntLE   = _primitive "<="
primIntGT   :: Int -> Int -> Bool
primIntGT   = _primitive ">"
primIntGE   :: Int -> Int -> Bool
primIntGE   = _primitive ">="

primFloatWAdd :: FloatW -> FloatW -> FloatW
primFloatWAdd  = _primitive "f+"
primFloatWSub :: FloatW -> FloatW -> FloatW
primFloatWSub  = _primitive "f-"
primFloatWMul :: FloatW -> FloatW -> FloatW
primFloatWMul  = _primitive "f*"
primFloatWDiv :: FloatW -> FloatW -> FloatW
primFloatWDiv = _primitive "f/"
primFloatWNeg :: FloatW -> FloatW
primFloatWNeg = _primitive "fneg"

primFloatWEQ :: FloatW -> FloatW -> Bool
primFloatWEQ = _primitive "f=="
primFloatWNE :: FloatW -> FloatW -> Bool
primFloatWNE = _primitive "f/="
primFloatWLT :: FloatW -> FloatW -> Bool
primFloatWLT = _primitive "f<"
primFloatWLE :: FloatW -> FloatW -> Bool
primFloatWLE = _primitive "f<="
primFloatWGT :: FloatW -> FloatW -> Bool
primFloatWGT = _primitive "f>"
primFloatWGE :: FloatW -> FloatW -> Bool
primFloatWGE = _primitive "f>="
primFloatWShow :: FloatW -> [Char]
primFloatWShow = _primitive "fshow"
primFloatWRead :: [Char] -> FloatW
primFloatWRead = _primitive "fread"
primFloatWFromInt :: Int -> FloatW
primFloatWFromInt = _primitive "itof"

primWordAdd :: Word -> Word -> Word
primWordAdd  = _primitive "+"
primWordSub :: Word -> Word -> Word
primWordSub  = _primitive "-"
primWordMul :: Word -> Word -> Word
primWordMul  = _primitive "*"
primWordQuot :: Word -> Word -> Word
primWordQuot = _primitive "uquot"
primWordRem :: Word -> Word -> Word
primWordRem  = _primitive "urem"
primWordAnd :: Word -> Word -> Word
primWordAnd  = _primitive "and"
primWordOr :: Word -> Word -> Word
primWordOr  = _primitive "or"
primWordXor :: Word -> Word -> Word
primWordXor  = _primitive "xor"
primWordShl :: Word -> Int -> Word
primWordShl  = _primitive "shl"
primWordShr :: Word -> Int -> Word
primWordShr  = _primitive "shr"
primWordAshr :: Word -> Int -> Word
primWordAshr  = _primitive "ashr"
primWordInv :: Word -> Word
primWordInv  = _primitive "inv"
primWordPopcount :: Word -> Int
primWordPopcount = _primitive "popcount"
primWordClz :: Word -> Int
primWordClz = _primitive "clz"
primWordCtz :: Word -> Int
primWordCtz = _primitive "ctz"
primWordToFloatWRaw :: Word -> FloatW
primWordToFloatWRaw = _primitive "toDbl"
primWordFromFloatWRaw :: FloatW -> Word
primWordFromFloatWRaw = _primitive "toInt"

primIntAnd :: Int -> Int -> Int
primIntAnd  = _primitive "and"
primIntOr :: Int -> Int -> Int
primIntOr  = _primitive "or"
primIntXor :: Int -> Int -> Int
primIntXor  = _primitive "xor"
primIntShl :: Int -> Int -> Int
primIntShl  = _primitive "shl"
primIntShr :: Int -> Int -> Int
primIntShr  = _primitive "ashr"
primIntInv :: Int -> Int
primIntInv  = _primitive "inv"
primIntPopcount :: Int -> Int
primIntPopcount = _primitive "popcount"
primIntClz :: Int -> Int
primIntClz = _primitive "clz"
primIntCtz :: Int -> Int
primIntCtz = _primitive "ctz"

primWordEQ  :: Word -> Word -> Bool
primWordEQ  = _primitive "=="
primWordNE  :: Word -> Word -> Bool
primWordNE  = _primitive "/="
primWordLT  :: Word -> Word -> Bool
primWordLT  = _primitive "u<"
primWordLE   :: Word -> Word -> Bool
primWordLE   = _primitive "u<="
primWordGT   :: Word -> Word -> Bool
primWordGT   = _primitive "u>"
primWordGE   :: Word -> Word -> Bool
primWordGE   = _primitive "u>="

primWordToInt :: Word -> Int
primWordToInt = _primitive "I"
primIntToWord :: Int -> Word
primIntToWord = _primitive "I"

-- Char is represented by Word
primCharEQ :: Char -> Char -> Bool
primCharEQ  = _primitive "=="
primCharNE :: Char -> Char -> Bool
primCharNE  = _primitive "/="
primCharLT :: Char -> Char -> Bool
primCharLT  = _primitive "u<"
primCharLE :: Char -> Char -> Bool
primCharLE  = _primitive "u<="
primCharGT :: Char -> Char -> Bool
primCharGT  = _primitive "u>"
primCharGE :: Char -> Char -> Bool
primCharGE  = _primitive "u>="

primFix    :: forall a . (a -> a) -> a
primFix    = _primitive "Y"

primSeq    :: forall a b . a -> b -> b
primSeq    = _primitive "seq"

--primEqual  :: forall a . a -> a -> Bool
--primEqual  = _primitive "equal"

-- Works for Int, Char, String
primStringCompare :: [Char] -> [Char] -> Ordering
primStringCompare  = _primitive "scmp"
primIntCompare :: Int -> Int -> Ordering
primIntCompare  = _primitive "icmp"
primCharCompare :: Char -> Char -> Ordering
primCharCompare  = _primitive "icmp"
primWordCompare :: Word -> Word -> Ordering
primWordCompare  = _primitive "ucmp"

primStringEQ  :: [Char] -> [Char] -> Bool
primStringEQ  = _primitive "sequal"

primChr :: Int -> Char
primChr = _primitive "chr"
primOrd :: Char -> Int
primOrd = _primitive "ord"

primUnsafeCoerce :: forall a b . a -> b
primUnsafeCoerce = _primitive "I"

primBind         :: forall a b . IO a -> (a -> IO b) -> IO b
primBind          = _primitive "IO.>>="
primThen         :: forall a b . IO a -> IO b -> IO b
primThen          = _primitive "IO.>>"
primReturn       :: forall a . a -> IO a
primReturn        = _primitive "IO.return"
primGetArgRef    :: IO (IOArray [[Char]])
primGetArgRef     = _primitive "IO.getArgRef"
primPerformIO    :: forall a . IO a -> a
primPerformIO     = _primitive "IO.performIO"

primRnfErr       :: forall a . a -> ()
primRnfErr        = _primitive "rnf" (0::Int)

primRnfNoErr     :: forall a . a -> ()
primRnfNoErr      = _primitive "rnf" (1::Int)

primWordToPtr :: forall a . Word -> Ptr a
primWordToPtr = _primitive "toPtr"

primPtrToWord :: forall a . Ptr a -> Word
primPtrToWord = _primitive "toInt"

primIntToPtr :: forall a . Int -> Ptr a
primIntToPtr = _primitive "toPtr"

primPtrToInt :: forall a . Ptr a -> Int
primPtrToInt = _primitive "toInt"

primFunPtrToWord :: forall a . FunPtr a -> Word
primFunPtrToWord = _primitive "toInt"

primIntToFunPtr :: forall a . Int -> FunPtr a
primIntToFunPtr = _primitive "toFunPtr"

primFunPtrToPtr :: forall a b . FunPtr a -> Ptr b
primFunPtrToPtr = _primitive "toPtr"

primPtrToFunPtr :: forall a b . Ptr a -> FunPtr b
primPtrToFunPtr = _primitive "toFunPtr"

-- Size in bits of Word/Int.
-- Will get constant folded on first use.
_wordSize :: Int
_wordSize = loop (primWordInv (0::Word)) (0::Int)
  where
    loop :: Word -> Int -> Int
    loop w n = if w `primWordEQ` (0::Word) then n else loop (primWordShr w (1::Int)) (n `primIntAdd` (1::Int))

-- Is this Windows?
foreign import ccall "iswindows" c_iswindows :: IO Int
_isWindows :: Bool
_isWindows = primPerformIO c_iswindows `primIntEQ` 1

primArrAlloc :: forall a . Int -> a -> IO (IOArray a)
primArrAlloc = _primitive "A.alloc"

primArrCopy :: forall a . IOArray a -> IO (IOArray a)
primArrCopy = _primitive "A.copy"

primArrSize :: forall a . IOArray a -> IO Int
primArrSize = _primitive "A.size"

primArrRead :: forall a . IOArray a -> Int -> IO a
primArrRead = _primitive "A.read"

primArrWrite :: forall a . IOArray a -> Int -> a -> IO ()
primArrWrite = _primitive "A.write"

-- Not referentially transparent
primArrEQ :: forall a . IOArray a -> IOArray a -> Bool
primArrEQ = _primitive "A.=="

primGC :: IO ()
primGC = _primitive "IO.gc"

primForeignPtrToPtr :: ForeignPtr a -> Ptr a
primForeignPtrToPtr = _primitive "fp2p"

primNewForeignPtr :: Ptr a -> IO (ForeignPtr a)
primNewForeignPtr = _primitive "fpnew"

primAddFinalizer :: FunPtr (Ptr a -> IO ()) -> ForeignPtr a -> IO ()
primAddFinalizer = _primitive "fpfin"

primForkIO :: IO () -> IO ThreadId
primForkIO = _primitive "IO.fork"

primMyThreadId :: IO ThreadId
primMyThreadId = _primitive "IO.thid"
primThreadNum :: ThreadId -> Word
primThreadNum = _primitive "thnum"

primYield :: IO ()
primYield = _primitive "IO.yield"

primMVarToWord :: forall a . MVar a -> Word
primMVarToWord = _primitive "toInt"

primNewEmptyMVar :: forall a . IO (MVar a)
primNewEmptyMVar = _primitive "IO.newmvar"
primTakeMVar :: forall a . MVar a -> IO a
primTakeMVar = _primitive "IO.takemvar"
primReadMVar :: forall a . MVar a -> IO a
primReadMVar = _primitive "IO.readmvar"
primPutMVar :: forall a . MVar a -> a -> IO ()
primPutMVar = _primitive "IO.putmvar"
primTryTakeMVar :: MVar a -> IO b {-(Maybe a)-}
primTryTakeMVar = _primitive "IO.trytakemvar"
primTryPutMVar :: MVar a -> a -> IO Bool
primTryPutMVar = _primitive "IO.tryputmvar"
primTryReadMVar :: MVar a -> IO b {-(Maybe a)-}
primTryReadMVar = _primitive "IO.tryreadmvar"

primThreadDelay :: Int -> IO ()
primThreadDelay = _primitive "IO.threaddelay"

primThreadStatus :: ThreadId -> IO Int
primThreadStatus = _primitive "IO.threadstatus"

primIsInt :: a -> Int
primIsInt = _primitive "isint"

primGetMaskingState :: IO Int
primGetMaskingState = _primitive "IO.getmaskingstate"
primSetMaskingState :: Int -> IO ()
primSetMaskingState = _primitive "IO.setmaskingstate"

primStats :: IO (Word, Word)
primStats = _primitive "IO.stats"
