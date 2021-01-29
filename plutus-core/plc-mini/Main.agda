module Main where

open import Haskell.Prelude hiding (_>>=_; _>>_; return)

open import Hutton

{-# FOREIGN AGDA2HS 
import Hutton
import Parser
import Prelude hiding (getContents)
import Data.ByteString.Lazy (getContents)
#-}

-- IO and friends are not in the prelude yet...
postulate
  IO : Set → Set
  _>>=_ : ∀{a b} → IO a → (a → IO b) → IO b
  _>>_ : ∀{a} → IO a → IO a → IO a
  return : ∀{a} → a → IO a
  putStrLn : String → IO ⊤

  ByteString : Set
  getContents : IO ByteString
  parseExp : ByteString → Maybe Exp
  pretty : Exp → String


-- do would be nicer...
main : IO ⊤
main = getContents >>= \b -> maybe
  (putStrLn "parse error")
  (putStrLn ∘ pretty ∘ Val ∘ eval)
  (parseExp b)

{-# COMPILE AGDA2HS main #-}


