{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TemplateHaskell #-}
{- 
  A small tutorial on Template Haskell as relevant to Plutus. It is split 
  split across two modules, `Tutorial.TH` (this module) and 
  `Tutorial.Emulator`, due to the staging restriction of Template Haskell. In 
  this module we will implement a function and in `Tutorial.Emulator` we will 
  use this function in a smart contract.

  Both modules are intended to be loaded in GHCi, GHC's interactive environment 
  (https://downloads.haskell.org/~ghc/latest/docs/html/users_guide/ghci.html).

  The problems in this module follow the numbering scheme E1, E2, etc. In many 
  places the `error` function is used to mark the spot where you need to fill 
  in the implementation.

  Some of the comments in this module contain GHCi commands. Each GHCi command
  is placed in a separate line prefixed by >>>, and its expected output (if any)
  is written in the following line.

  After making changes to the source file (TH.hs) you can type `:r` in 
  GHCi to load the changes.

  The topics covered by the exercises are
  * GHCi
  * Template Haskell (quote, unquote)
  * Compiling plutus programs
  * Testing smart contracts in GHCi

-}
module Tutorial.TH where

import           Language.Haskell.TH

{- |
  Part 1. Template Haskell

  Let's implement a variation of the guessing game: Instead of a hash 
  function we will use a custom `tricky :: Int -> Int` function to compute
  the secret. It is called "tricky" because one cannot easily compute the 
  inverse of "tricky" in one's head. (although it is not nearly as 
  tricky as computing the inverse of `sha256`)

-}

tricky :: Q (TExp (Int -> Int))
tricky = [|| \i -> 2 * i - i * i + 5 * i * i * i - 6 * i * i * i - 8 ||]

{- |
    E1: Test `tricky` in the repl (ghci) on various values

    >>> :set -XTemplateHaskell
    >>> $$(tricky) 1
    -8
    >>> $$(tricky) 0
    -8
    >>> $$(tricky) 11
    -1438
-}

{- |

    To make the function even harder to invert we apply it a number of times 
    in a row. 

    E2: Implement `trickier` so that
    * `$$(trickier 1) i` is `$$(tricky) i` and
    * `$$(trickier (n + 1)) i` is `$$(tricky) ($$(trickier n) i)`.

    Then test it in GHCi.
-}
trickier :: Int -> Q (TExp (Int -> Int))
trickier i = if i <= 1 then tricky else [|| error "exercise" ||]

{- 

  The rest of this tutorial can be found in Emulator.hs. We cannot use 
  'trickier' in the same module where it is defined.

-}