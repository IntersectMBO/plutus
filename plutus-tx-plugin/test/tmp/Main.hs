{-# LANGUAGE BangPatterns    #-}
{-# LANGUAGE DataKinds       #-}
{-# LANGUAGE TemplateHaskell #-}
-- {-# OPTIONS_GHC -fenable-rewrite-rules #-}
-- {-# OPTIONS_GHC -ddump-rules #-}
-- {-# OPTIONS_GHC -ddump-rule-firings #-}
-- {-# OPTIONS_GHC -ddump-simpl #-}

{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:context-level=0 #-}

module Main
where


import PlutusTx
import PlutusTx.Prelude
-- import PlutusTx.Enum
import Prelude qualified as H


-- $$(compile [|| [ y+3 | y <- [ x*x | x <- [1..5]::[Integer] ] ] ||])

main :: H.IO ()
main =
   let !_ = $$(compile [|| [1..99] ::[Integer] ||])
   in H.pure ()


