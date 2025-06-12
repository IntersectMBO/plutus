module PrimTable(module PrimTable) where
import Control.Exception
import Data.Bits
import Data.Char
import Data.Maybe
import Data.Word
import Foreign.C.String
import Foreign.C.Types
import Foreign.Marshal.Alloc
import Foreign.Ptr
import GHC.Types (Any)
import System.IO
import System.IO.TimeMilli
import Unsafe.Coerce
--import System.Environment
import System.IO.Unsafe
--import Debug.Trace

type AnyType = Any

_primitive :: String -> Any
--primitive s | trace ("_primitive " ++ show s) False = undefined
_primitive "dynsym" = unsafeCoerce dynsym
_primitive s        = fromMaybe (error $ "PrimTable._primitive: " ++ s) $ lookup s primOps

primOps :: [(String, Any)]
primOps =
  [ comb "S" (\ f g x -> f x (g x))
  , comb "K" const
  , comb "I" id
  , comb "B" (\ f g x -> f (g x))
  , comb "C" (\ f g x -> f x g)
  , comb "S'" (\ k f g x -> k (f x) (g x))
  , comb "B'" (\ k f g x -> k f (g x))
  , comb "C'" (\ k f g x -> k (f x) g)
  , comb "A" (\ _x y -> y)
  , comb "U" (\ x y -> y x)
  , comb "Y" (\ f -> let r = f r in r)
  , comb "Z" (\ f g _x -> f g)
  , comb "J" (\ x _y z -> z x)
  , comb "P" (\ x y f -> f x y)
  , comb "R" (\ x y f -> y f x)
  , comb "O" (\ x y _g f -> f x y)
  , comb "K2" (\ x _y _z -> x)
  , comb "K3" (\ x _y _z _w -> x)
  , comb "K4" (\ x _y _z _w _v -> x)
  , comb "C'B" (\ x y z w -> x z (y w))

  , arith "+" (+)
  , arith "-" (-)
  , arith "*" (*)
  , arith "quot" quot
  , arith "rem" rem
  , arith "subtract" subtract
  , arithu "neg" negate
  , arithu "inv" complement
  , arithw "uquot" quot
  , arithw "urem" rem
  , arithw "and" (.&.)
  , arithw "or" (.|.)
  , arithw "xor" xor
  , arithwi "shl" shiftL
  , arithwi "shr" shiftR
  , arith "ashr" shiftR
  , arithu "popcount" popCount
  , arithu "clz" countLeadingZeros
  , arithu "ctz" countTrailingZeros
  , cmp "==" (==)
  , cmp "/=" (/=)
  , cmp "<"  (<)
  , cmp "<=" (<=)
  , cmp ">"  (>)
  , cmp ">=" (>=)
  , cmpw "u<"  (<)
  , cmpw "u<=" (<=)
  , cmpw "u>"  (>)
  , cmpw "u>=" (>=)
  , comb "icmp" (\ x y -> fromOrdering (compare (x::Int) y))

  , comb "scmp" (\ x y -> fromOrdering (compare (toString x) (toString y)))
  , comb "sequal" (\ x y -> fromBool (toString x == toString y))

  , comb "p==" (\ x y -> fromBool ((x :: Ptr ()) == y))
  , comb "pnull" nullPtr
  , comb "pcast" castPtr
  , comb "p+" plusPtr
  , comb "p-" minusPtr

  , farith "f+" (+)
  , farith "f-" (-)
  , farith "f*" (*)
  , farith "f/" (/)
  , farithu "fneg" negate
  , fcmp "f==" (==)
  , fcmp "f/=" (/=)
  , fcmp "f<" (<)
  , fcmp "f<=" (<=)
  , fcmp "f>" (>)
  , fcmp "f>=" (>=)
  , comb "fshow" (fromString . (show :: Double -> String))
  , comb "fread" ((read :: String -> Double) . toString)
  , comb "itof" (fromIntegral :: Int -> Double)

  , comb "seq" seq
  , comb "rnf" rnf
  , comb "error" err
  , comb "ord" ord
  , comb "chr" chr

  , comb "IO.performIO" unsafePerformIO
  , comb "IO.catch" (\ io hdl -> Control.Exception.catch (io :: IO Any) (\ (exn :: Exception) -> hdl (fromString $ takeWhile (/= '\n') $ show exn) :: IO Any))
  , comb "IO.>>=" iobind
  , comb "IO.>>" iothen
  , comb "IO.return" ioret
  , comb "IO.print" ioprint
  , comb "IO.performio" unsafePerformIO
  , comb "IO.serialize" ioserialize
  , comb "IO.deserialize" iodeserialize
  , comb "newCAStringLen" (fmap fromPair . newCAStringLen . toString)
  , comb "IO.getArgRef" iogetargref

  , comb0 "IO.stdin" stdin
  , comb0 "IO.stdout" stdout
  , comb0 "IO.stderr" stderr

  ]
  where
    comb0 n f = (n, unsafeCoerce f)
    comb n f = (n, unsafeCoerce f)
--    comb n f = (n, unsafeCoerce (\ x -> trace (seq x n) (f x)))
    arith :: String -> (Int -> Int -> Int) -> (String, Any)
    arith = comb
    arithw :: String -> (Word -> Word -> Word) -> (String, Any)
    arithw = comb
    arithwi :: String -> (Word -> Int -> Word) -> (String, Any)
    arithwi = comb
    arithu :: String -> (Int -> Int) -> (String, Any)
    arithu = comb
    farith :: String -> (Double -> Double -> Double) -> (String, Any)
    farith = comb
    farithu :: String -> (Double -> Double) -> (String, Any)
    farithu = comb
    cmp :: String -> (Int -> Int -> Bool) -> (String, Any)
    cmp n f = comb n (\ x y -> fromBool (f x y))
    cmpw :: String -> (Word -> Word -> Bool) -> (String, Any)
    cmpw n f = comb n (\ x y -> fromBool (f x y))
    fcmp :: String -> (Double -> Double -> Bool) -> (String, Any)
    fcmp n f = comb n (\ x y -> fromBool (f x y))

    err s = error $ "error: " ++ toString s

    iobind :: IO a -> (a -> IO b) -> IO b
    iobind = (>>=)
    iothen :: IO a -> IO b -> IO b
    iothen = (>>)
    ioret :: a -> IO a
    ioret = return
    -- Can't implement this
    ioprint :: Handle -> a -> IO ()
    ioprint h _ = hPutStrLn h "hugs does not support cprint"
    ioserialize :: Handle -> a -> IO ()
    ioserialize h _ = hPutStrLn h "hugs does not support serialize"
    iodeserialize :: Handle -> IO a
    iodeserialize _ = error "hugs does not support deserialize"

{-
    iogetargs :: IO Any
    iogetargs = do
      args <- getArgs
      return $ fromList $ map fromString args
-}
    iogetargref = error "hugs: no IO.getArgRef"

    -- Can't implement this
    rnf :: a -> ()
    rnf x = seq x ()

fromBool :: Bool -> Any
fromBool False = unsafeCoerce const
fromBool True  = unsafeCoerce $ \ _x y -> y

fromOrdering :: Ordering -> (Any -> Any -> Any -> Any)
fromOrdering LT = \ x _y _z -> x
fromOrdering EQ = \ _x y _z -> y
fromOrdering GT = \ _x _y z -> z

fromPair :: (a, b) -> Any
fromPair (x, y) = unsafeCoerce $ \ pair -> pair x y

fromString :: String -> Any
fromString = fromList . map (unsafeCoerce . ord)

fromList :: [Any] -> Any
fromList []     = unsafeCoerce const
fromList (x:xs) = unsafeCoerce $ \ _nil cons -> cons (unsafeCoerce x) (fromList xs)

toList :: Any -> [Int]
toList a = unsafeCoerce a [] (\ i is -> i : toList is)

toString :: Any -> String
toString = map chr . toList

dynsym :: Any -> Any
dynsym acfun =
  let s = toString acfun
  in
--      trace ("dynsym: " ++ show s) $
      fromMaybe (error $ "hugs: unimplemented FFI: " ++ s) $ lookup s cops

popCount :: Int -> Int
popCount = undefined

countLeadingZeros :: Int -> Int
countLeadingZeros = undefined

countTrailingZeros :: Int -> Int
countTrailingZeros = undefined

cops :: [(String, Any)]
cops =
  [ comb "getTimeMilli" getTimeMilli
  , comb "fputc" fputc
  , comb "fgetc" fgetc
  , comb "fopen" fopen
  , comb "fclose" fclose
  , comb "putb"  putb
  , comb "add_FILE" add_FILE
  , comb "add_utf8" add_utf8
  , comb "free"  free
  , comb "exp"   (fio exp)
  , comb "log"   (fio log)
  , comb "sqrt"   (fio sqrt)
  , comb "sin"   (fio sin)
  , comb "cos"   (fio cos)
  , comb "tan"   (fio tan)
  , comb "asin"   (fio asin)
  , comb "acos"   (fio acos)
  , comb "atan"   (fio atan)
  , comb "sinh"   (fio sinh)
  , comb "cosh"   (fio cosh)
  , comb "tanh"   (fio tanh)
  , comb "asinh"   (fio asinh)
  , comb "acosh"   (fio acosh)
  , comb "atanh"   (fio atanh)
  , comb "atan2"   (fio2 atan2)
  ]
  where
    comb n f = (n, unsafeCoerce f)

    fio :: (Double -> Double) -> (Double -> IO Double)
    fio f = return . f

    fio2 :: (Double -> Double -> Double) -> (Double -> Double -> IO Double)
    fio2 f x y = return (f x y)

    add_FILE :: Handle -> IO Handle
    add_FILE h = return h

    add_utf8 :: Handle -> IO Handle
    add_utf8 h = do {-hSetEncoding h utf8;-} return h

    putb :: Int -> Handle -> IO ()
    putb c h = hPutChar h (chr c)

    fputc :: Int -> Handle -> IO Int
    fputc c h = hPutChar h (chr c) >> return 0

    fgetc :: Handle -> IO Int
    fgetc h = handle (\ (_ :: Exception) -> return (-1)) (do c <- hGetChar h; return (ord c))

    fopen :: Ptr CChar -> Ptr CChar -> IO Handle
    fopen name mode = do
      sname <- peekCAString name
      smode <- peekCAString mode
      let hmode =
            case smode of
              "r"  -> ReadMode
              "w"  -> WriteMode
              "a"  -> AppendMode
              "w+" -> ReadWriteMode
              _    -> error "fopen"
      openFile sname hmode

    fclose :: Handle -> IO Int
    fclose h = do hClose h; return 0
