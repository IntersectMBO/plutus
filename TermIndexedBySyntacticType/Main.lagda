\begin{code}
module TermIndexedBySyntacticType.Main where
open import Agda.Builtin.IO
open import Agda.Builtin.Unit
open import Agda.Builtin.String

postulate
  putStrLn : String → IO ⊤

{-# FOREIGN GHC import qualified Data.Text.IO as Text #-}
{-# COMPILE GHC putStrLn = Text.putStrLn #-}

open import Builtin.Constant.Term
open import Builtin.Constant.Type
open import Builtin.Signature
open import Type
open import TermIndexedBySyntacticType.Term
open import TermIndexedBySyntacticType.Evaluation
open import TermIndexedBySyntacticType.Term.Reduction

--open import TermIndexedBySyntacticType.Examples

open import Agda.Builtin.TrustMe
open import Relation.Binary.PropositionalEquality
open import Agda.Builtin.Nat
open import Data.Nat
open import Agda.Builtin.Int
open import Data.Integer

open import Data.Product renaming (_,_ to _,,_)

lemma : length empty ≡ 0
lemma = primTrustMe

conE : ∀{Γ} → Γ ⊢ con bytestring (size⋆ 8)
conE = con (bytestring 8 empty (subst (λ n → Data.Nat.suc n Data.Nat.≤ 8) (sym lemma) (s≤s z≤n)))

appendE : ∀{Γ} → Γ ⊢ con bytestring (size⋆ 8)
appendE = builtin concatenate (λ { Z → size⋆ 8 ; (S ())}) (conE ,, conE ,, tt)

con1 : ∀{Γ} → Γ ⊢ con integer (size⋆ 8)
con1 = con (integer 8 (pos 1) (-≤+ ,, (+≤+ (s≤s (s≤s z≤n))))) -- (-≤+ ,, (+≤+ (s≤s (s≤s z≤n)))))

con2 : ∀{Γ} → Γ ⊢ con integer (size⋆ 8)
con2 = con (integer 8 (pos 2) (-≤+ ,, (+≤+ (s≤s (s≤s (s≤s z≤n)))))) -- (-≤+ ,, +≤+ (s≤s (s≤s (s≤s z≤n)))))

builtin2plus2 : ∅ ⊢ con integer (size⋆ 8)
builtin2plus2 = builtin
  addInteger
  (λ { Z → size⋆ 8 ; (S x) → ` x})
  (con2 ,, con2 ,, tt)

inc8 : ∅ ⊢ con integer (size⋆ 8) ⇒ con integer (size⋆ 8)
inc8 = ƛ (builtin
  addInteger
  (λ { Z → size⋆ 8 ; (S x) → ` x})
  (con1 ,, ` Z ,, tt))

builtininc2 : ∅ ⊢ con integer (size⋆ 8)
builtininc2 = inc8 · con2

inc : ∅ ⊢ Π (con integer (` Z) ⇒ con integer (` Z))
inc = Λ (ƛ (builtin addInteger ` ((builtin resizeInteger (λ { Z → ` Z ; (S Z) → size⋆ 8 ; (S (S ()))}) (builtin sizeOfInteger ` (` Z ,, tt) ,, (con1 ,, tt))) ,, (` Z) ,, tt)))

builtininc2' : ∅ ⊢ con integer (size⋆ 8)
builtininc2' = (inc ·⋆ size⋆ 8) · con2

printCon : (x : ∅ ⊢ con integer (size⋆ 8)) → Value x → ℤ
printCon .(con (integer 8 i x)) (V-con (integer .8 i x)) = i

main : IO ⊤
main with eval (gas 100) builtin2plus2
main | steps x (done n v) = putStrLn (show (printCon n v))
main | steps x out-of-gas = putStrLn "out of gas..."
main | error              = putStrLn "something went wrong..."
\end{code}
