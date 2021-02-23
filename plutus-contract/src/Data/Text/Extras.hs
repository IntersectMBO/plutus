{-# LANGUAGE OverloadedStrings #-}

module Data.Text.Extras(
      abbreviate
    , tshow
    ) where

import qualified Data.Text as T

tshow :: Show a => a -> T.Text
tshow = T.pack . show

abbreviate :: Int -> T.Text -> T.Text
abbreviate n txt
    | n <= 0 = ""
    | T.length txt > n = T.take (n - 1) txt <> "…"
    | otherwise = txt
