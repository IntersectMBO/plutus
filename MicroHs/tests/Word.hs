module Word(main) where
import Data.Word

vals :: [Word16]
vals = [0xfff0, 0xfffe, 0xffff, 0, 1, 2, 5]

maxw :: Word
maxw = if _wordSize == 32 then 0x7fff::Word else 0x7fffffff::Word

main :: IO ()
main = do
  print (1000::Word)
  print $ maxw*maxw > 0
  print [ op x y | x <- vals, y <- vals, op <- [(+),( - ),(*)] ]
  print [ op x y | x <- vals, y <- vals, y /= 0, op <- [quot, rem] ]
  print [ op x y | x <- vals, y <- vals, op <- [(==),(/=),(<),(<=),(>),(>=)] ]
  print [ op x y | x <- vals, y <- vals, let op = compare ]
