module Unicode(main) where
import Data.Char

main :: IO ()
main = do
  putStrLn "abc"
  putStrLn "\xe5\&bc"
  putStrLn "\x402\xa88"
  writeFile "unicode.tmp" "\xe5\&bc"
  ustr <- readFile "unicode.tmp"
  print $ ustr == "\xe5\&bc"
  let a = "å ä ö"
  putStrLn a
  print $ map isLower a
  print $ map isUpper a
  putStrLn $ map toUpper a
  print $ map (isUpper . toUpper) a

  let printCases c = putStrLn $ toLower c : toTitle c : toUpper c : ""
  printCases '\x01C4' -- upper
  printCases '\x01C5' -- title
  printCases '\x01C6' -- lower
  printCases '\x2168' -- IX
  printCases '\x2178' -- ix

foo ∷ ∀ α . Eq α ⇒ α → α
foo x = if x == x then x else undefined
