module Main where

open import Haskell.Prelude hiding (_>>=_; _>>_; return)

open import Lang
{-# FOREIGN AGDA2HS import Lang #-}

{-# FOREIGN AGDA2HS import Parser #-}
{-# FOREIGN AGDA2HS import Prelude hiding (getContents) #-}
{-# FOREIGN AGDA2HS import Data.ByteString.Lazy (getContents) #-}


postulate
  IO : Set → Set
  _>>=_ : ∀{a b} → IO a → (a → IO b) → IO b
  _>>_ : ∀{a} → IO a → IO a → IO a
  return : ∀{a} → a → IO a
  putStrLn : String → IO ⊤


  ByteString : Set
  getContents : IO ByteString
  parse : ByteString → Maybe Exp
  pretty : Exp → String

main : IO ⊤
main = getContents >>= \b -> maybe
  (putStrLn "parse error")
  (putStrLn ∘ pretty ∘ Val ∘ eval)
  (parse b)

{-# COMPILE AGDA2HS main #-}


