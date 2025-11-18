{-# LANGUAGE LambdaCase #-}

module PlutusBenchmark.NaturalSort (naturalSort)
where

import Data.Char (isDigit)
import Data.List (sortBy)

{-| If we have the list of file names ["multisig-sm-1", "multisig-sm-2",
   "multisig-sm-10"] then Haskell's standard 'sort' function will return
   ["multisig-sm-1", "multisig-sm-10", "multisig-sm-2"], which is annoying.  The
   'naturalSort' function here sorts it into the order you'd probably expect.
   It does this by splitting strings into sequences of numeric and non-numeric
   substrings and then comparing those sequences. -}
data Component
  = Numeric Int
  | Other String
  deriving stock (Eq, Ord, Show)

-- Numeric < Other

getComponent :: String -> Maybe (Component, String)
getComponent "" = Nothing
getComponent s@(c : _)
  | isDigit c =
      case span isDigit s of
        (p, q) -> Just (Numeric (read p), q)
  | otherwise =
      case span (not . isDigit) s of
        (p, q) -> Just (Other p, q)

toComponents :: String -> [Component]
toComponents s =
  case getComponent s of
    Nothing -> []
    Just (p, q) -> p : (toComponents q)

{- Compare two strings according to their components.  A difficulty arises
   because, for example, "file1" and "file01" have the same components but aren't
   equal: in cases like that we fall back on the original string ordering.  This
   gives us, eg

   "file" < "file0" < "file00" < "file000" < "file001" < "file01" < "file1" < "file02"

   The standard ordering would be the same except that we'd have "file01" < "file02" < "file1"
   at the end
-}
naturalCompare :: String -> String -> Ordering
naturalCompare s1 s2 =
  let c1 = toComponents s1
      c2 = toComponents s2
   in if c1 == c2
        then compare s1 s2
        else compare c1 c2

naturalSort :: [String] -> [String]
naturalSort = sortBy naturalCompare
