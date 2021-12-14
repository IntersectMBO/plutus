{-# LANGUAGE TemplateHaskell   #-}

-- | This module is to test issue
-- https://github.com/haskell-foundation/foundation/issues/326
--
-- this test has been originaly proposed by https://github.com/RyanGlScott
-- in comment of the issue 326:
-- https://github.com/haskell-foundation/foundation/issues/326#issuecomment-309219955

module Main (main) where

import Foundation as F
import Language.Haskell.TH

main :: IO ()
main = $(do runIO $ F.putStrLn (F.fromString "Hello")
            [| return () |])
