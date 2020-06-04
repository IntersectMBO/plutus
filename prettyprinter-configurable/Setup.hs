{-# LANGUAGE CPP #-}

module Main where

-- That's how people do that. I don't know why.
#ifndef MIN_VERSION_cabal_doctest
#define MIN_VERSION_cabal_doctest(x,y,z) 0
#endif

#if MIN_VERSION_cabal_doctest(1,0,0)

import           Distribution.Extra.Doctest (defaultMainWithDoctests)

main :: IO ()
main = defaultMainWithDoctests "prettyprinter-configurable-doctest"

#else

import           Distribution.Simple

main :: IO ()
main = defaultMain

#endif
