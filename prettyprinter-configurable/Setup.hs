{-# LANGUAGE CPP #-}

module Main where

-- That's how people do that. I don't know why.
#ifndef MIN_VERSION_cabal_doctest
#define MIN_VERSION_cabal_doctest(x,y,z) 0
#endif

-- stylish-haskell is unable to parse import lines that are interspersed with
-- other code, hence why we resort to using two #ifs instead of one.

#if MIN_VERSION_cabal_doctest(1,0,0)
import Distribution.Extra.Doctest (defaultMainWithDoctests)
#else
import Distribution.Simple
#endif

#if MIN_VERSION_cabal_doctest(1,0,0)
main :: IO ()
main = defaultMainWithDoctests "prettyprinter-configurable-doctest"
#else
main :: IO ()
main = defaultMain
#endif

