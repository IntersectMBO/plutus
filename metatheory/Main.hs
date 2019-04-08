module Main where

import qualified MAlonzo.Code.Main as M

-- Cabal, unlike GHC, does not appear to allow the main function to be
-- in module whose name isn't Main. This little file is a workaround.

main = M.main
