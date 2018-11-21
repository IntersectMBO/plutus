\begin{code}
module TermIndexedByNormalType.Main where
open import Agda.Builtin.IO
open import Agda.Builtin.Unit
open import Agda.Builtin.String

open import Type
open import Type.BetaNormal
open import TermIndexedByNormalType.Term
open import TermIndexedByNormalType.Evaluation
postulate
  putStrLn : String → IO ⊤

{-# FOREIGN GHC import qualified Data.Text.IO as Text #-}
{-# COMPILE GHC putStrLn = Text.putStrLn #-}

N : ∀{Γ} → Γ ⊢Nf⋆ *
N = Π ((ne (` Z)) ⇒ (ne (` Z) ⇒ ne (` Z)) ⇒ (ne (` Z)))

Zero : ∅ ⊢ N
Zero = Λ (ƛ (ƛ (` (S Z))))

Succ : ∅ ⊢ N ⇒ N
Succ = ƛ (Λ (ƛ (ƛ (` Z · ((` (S (S (T Z)))) ·⋆ (ne (` Z)) · (` (S Z)) · (` Z))))))

One : ∅ ⊢ N
One = Succ · Zero

Two : ∅ ⊢ N
Two = Succ · One

TwoPlusTwo' : ∅ ⊢ N
TwoPlusTwo' = Two ·⋆ N · Two · Succ

main : IO ⊤
main with eval (gas 100) TwoPlusTwo'
main | steps x (done _ _) = putStrLn "it worked!"
main | steps x out-of-gas = putStrLn "out of gas..."
\end{code}
