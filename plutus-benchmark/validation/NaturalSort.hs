{-# LANGUAGE LambdaCase #-}

module NaturalSort (naturalSort)
where

import           Data.Char
import           Data.List

{- | If we have the list of file names ["multisig-sm-1", "multisig-sm-2",
   "multisig-sm-10"] then Haskell's standard 'sort' function will return
   ["multisig-sm-1", "multisig-sm-10", "multisig-sm-2"], which is annoying.  The
   'naturalSort' function here sorts it into the order you'd probably expect.
   It does this by splitting strings into sequences of numeric and non-numeric
   substrings and then comparing those sequences.
-}

data Component =
    Numeric Int
  | Other String
    deriving (Eq, Ord, Show)
    -- Numeric < Other

fromComponents :: [Component] -> String
fromComponents = concatMap (\case Numeric n -> show n; Other s -> s)

getComponent :: String -> Maybe (Component, String)
getComponent "" = Nothing
getComponent s@(c:cs)
    | isDigit c =
        case span isDigit s of
          (p,q) -> Just (Numeric (read p), q)
    | otherwise =
        case span (not . isDigit) s of
          (p,q) -> Just (Other p, q)

toComponents :: String -> [Component]
toComponents s =
    case getComponent s of
      Nothing    -> []
      Just (p,q) -> p : (toComponents q)

naturalSort :: [String] -> [String]
naturalSort l = map fromComponents $ sort (map toComponents l)
