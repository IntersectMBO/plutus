module Main where

import Test.DocTest
import Prelude

main :: IO ()
main = doctest (extensions ++ flags ++ files)

extensions :: [String]
extensions =
  [ "-XBangPatterns"
  , "-XDeriveDataTypeable"
  , "-XNoImplicitPrelude"
  , "-XRebindableSyntax"
  , "-XOverloadedStrings"
  , "-XTypeFamilies"
  ]

flags :: [String]
flags = ["-fobject-code"]

-- Would be nice to just use "src" here, but both Basement.String and
-- Foundation.String.UTF8LL share the same module name, and doctest breaks.
files :: [String]
files =
  [ "Foundation/Collection/Buildable.hs"
  , "Foundation/VFS/FilePath.hs"
  , "Foundation/VFS/Path.hs"
  ]
