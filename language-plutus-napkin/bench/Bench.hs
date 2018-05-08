{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import           Criterion.Main
import qualified Data.ByteString.Lazy                  as BSL
import           Data.Text.Prettyprint.Doc             (defaultLayoutOptions,
                                                        layoutSmart)
import           Data.Text.Prettyprint.Doc.Render.Text (renderStrict)
import           Language.PlutusCore

tinyProgram :: BSL.ByteString
tinyProgram = "[(builtin addInteger) x y]"

main :: IO ()
main =
    defaultMain [ bgroup "format"
                      [ bench "format" $ nf (fmap (renderStrict . layoutSmart defaultLayoutOptions) . format) tinyProgram ]
                , bgroup "parse"
                      [ bench "parse" $ nf parse tinyProgram ]
                ]
