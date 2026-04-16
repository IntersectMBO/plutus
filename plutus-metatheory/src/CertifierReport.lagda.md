---
title: Certifier Report
layout: page
---
# Certifier Report

```
module CertifierReport where

open import VerifiedCompilation
open import VerifiedCompilation.Certificate
open import VerifiedCompilation.UntypedTranslation
open import VerifiedCompilation.UInline
open import Untyped
open import Untyped.RenamingSubstitution using (Sub)
open import Utils as U using (_×_; _,_; Either; either; inj₁; inj₂)

open import Agda.Builtin.Sigma using (Σ; _,_; snd)
open import Data.Bool using (if_then_else_)
open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Binary.Pointwise.Base using (Pointwise)
open import Data.Maybe
open import Data.Nat
open import Data.Nat.Show using () renaming (show to showℕ)
open import Data.String using (String; _++_)

infix 0 ⇉_

⇉_ : String → String
⇉ s = "  " ++ s

nl : String
nl = "\n"

hl : String
hl = "\n──────────────────────────────────────────────────────\n"

showCertifiedOptTag : CertifiedOptTag → String
showCertifiedOptTag floatDelayT = "Float Delay"
showCertifiedOptTag forceDelayT = "Force-Delay Cancellation"
showCertifiedOptTag forceCaseDelayT = "Float Force into Case Branches"
showCertifiedOptTag caseReduceT = "Case-Constr and Case-Constant Cancellation"
showCertifiedOptTag inlineT = "Inlining"
showCertifiedOptTag cseT = "Common Subexpression Elimination"
showCertifiedOptTag applyToCaseT = "Transform multi-argument applications into case-constr form"

showUncertifiedOptTag : UncertifiedOptTag → String
showUncertifiedOptTag caseOfCaseT = "Case-of-Case"
showUncertifiedOptTag letFloatOutT = "Float bindings outwards"

showTag : OptTag → String
showTag (inj₁ tag) = showUncertifiedOptTag tag ++ "  ⚠ (certifier unavailable)"
showTag (inj₂ tag) = showCertifiedOptTag tag ++ "  ✅"
```

Number of times an optimization is applied on the given term in one compiler pass:

```
numSites′ : {R : Relation} {M N : 0 ⊢} → Translation R M N → ℕ
numSites′ = go 0
  where
  go : {R : Relation} {X : ℕ} {M N : X ⊢} →  ℕ → Translation R M N → ℕ
  goᵐ : {R : Relation} {X : ℕ} {M N : X ⊢} →  ℕ → TransMatch R M N → ℕ
  goᵖʷ : {R : Relation} {X : ℕ} {Ms Ns : List (X ⊢)} → ℕ → Pointwise (Translation R) Ms Ns → ℕ

  go n (istranslation _) = suc n
  go n (match m) = goᵐ n m

  goᵐ n var = n
  goᵐ n (ƛ t) = go n t
  goᵐ n (app f a) = go (go n f) a
  goᵐ n (force t) = go n t
  goᵐ n (delay t) = go n t
  goᵐ n (constr xs) = goᵖʷ n xs
  goᵐ n (case xs x) = go (goᵖʷ n xs) x
  goᵐ n con = n
  goᵐ n builtin = n
  goᵐ n error = n

  goᵖʷ n Pointwise.[] = n
  goᵖʷ n (x Pointwise.∷ xs) = goᵖʷ (go n x) xs

numSitesInlineᵖʷ :
  {X : ℕ}
  {σ : Sub X X}
  {Ms Ns : List (X ⊢)}
  (p : Pointwise (Inline σ □) Ms Ns)
  → ℕ

numSitesInline :
  {X : ℕ}
  {σ : Sub X X}
  {z z′ : X ↝}
  {zz : z ≽ z′}
  {M M′ : X ⊢}
  (p : Inline σ zz M M′)
  → ℕ
numSitesInline (` x) = 0
numSitesInline (`↓ r) = numSitesInline r + 1
numSitesInline (ƛ□ r) = numSitesInline r
numSitesInline (ƛ r) = numSitesInline r
numSitesInline (ƛ↓ r) = numSitesInline r
numSitesInline (r · s) = numSitesInline r + numSitesInline s
numSitesInline (r ·↓) = numSitesInline r
numSitesInline (force r) = numSitesInline r
numSitesInline (delay r) = numSitesInline r
numSitesInline con = 0
numSitesInline builtin = 0
numSitesInline error = 0
numSitesInline (constr rs) = numSitesInlineᵖʷ rs
numSitesInline (case r rs) = numSitesInline r + numSitesInlineᵖʷ rs

numSitesInlineᵖʷ Pointwise.[] = 0
numSitesInlineᵖʷ (x Pointwise.∷ xs) = numSitesInline x + numSitesInlineᵖʷ xs

numSites : {M N : 0 ⊢} (tag : CertifiedOptTag) → RelationOf (inj₂ tag) M N → ℕ
numSites forceDelayT p = numSites′ p
numSites floatDelayT p = numSites′ p
numSites cseT p = numSites′ p
numSites caseReduceT p = numSites′ p
numSites inlineT p = numSitesInline p
numSites forceCaseDelayT p = numSites′ p
numSites applyToCaseT p = numSites′ p

showSites : {M N : 0 ⊢} → (tag : OptTag) → RelationOf tag M N → String
showSites (inj₁ _) _ = ""
showSites (inj₂ t) p = ⇉ "Optimization sites: " ++ showℕ (numSites t p)

termSize : {X : ℕ} → X ⊢ → ℕ
termSizeᵖʷ : {X : ℕ} → List (X ⊢) → ℕ

termSize (` _) = 1
termSize (ƛ M) = 1 + termSize M
termSize (M · N) = 1 + termSize M + termSize N
termSize (force M) = 1 + termSize M
termSize (delay M) = 1 + termSize M
termSize (con _) = 1
termSize (builtin _) = 1
termSize error = 1
termSize (constr _ Ms) = 1 + termSizeᵖʷ Ms
termSize (case M Ms) = 1 + termSize M + termSizeᵖʷ Ms

termSizeᵖʷ [] = 0
termSizeᵖʷ (x ∷ xs) = termSize x + termSizeᵖʷ xs
```

Functions for producing the certifier report:

```
showEvalResult : EvalResult → String
showEvalResult (success cpu mem) =
  (⇉ "Execution Cost: CPU = ") ++ showℕ cpu ++ ", MEM = " ++ showℕ mem
showEvalResult (failure err cpu mem) =
  (⇉ "Evaluation FAILED: ") ++ err ++
  nl ++
  (⇉ "Execution Cost: CPU = ") ++ showℕ cpu ++ ", MEM = " ++ showℕ mem

showCostPair : List EvalResult → String
showCostPair (x ∷ y ∷ _) =
  showEvalResult x ++ " (before)" ++
  nl ++
  showEvalResult y ++ " (after)"
showCostPair _ = ""

tail : {A : Set} → List A → List A
tail (_ ∷ rest) = rest
tail [] = []

reportPasses :
  (n : ℕ)
  (t : Trace (0 ⊢))
  (r : Certificate t)
  → List EvalResult
  → String
reportPasses _ (done _) _ _ = ""
reportPasses n (step tag _ x trace) (p , proofs) costs =
  hl ++
  "Pass " ++ showℕ n ++ ": " ++ showTag tag ++
  hl ++
  (⇉ "Program Size: ") ++ showℕ (termSize x) ++ " (before)" ++
  nl ++
  (⇉ "Program Size: ") ++ showℕ (termSize (head trace)) ++ " (after)" ++
  nl ++
  showCostPair costs ++
  nl ++
  showSites tag p ++
  nl ++
  reportPasses (suc n) trace proofs (tail costs)

reportFailure : Error → String
reportFailure (counterExample tag) =
  hl ++
  "Pass " ++ showTag tag ++ "  ❌ FAILED" ++
  hl
reportFailure (abort tag) =
  hl ++
  "Pass " ++ showTag tag ++ "  ❌ FAILED" ++
  hl
reportFailure emptyDump =
  hl ++
  "Empty trace from the compiler  ❌ FAILED" ++
  hl
reportFailure illScoped =
  hl ++
  "Trace from compiler contained ill-scoped terms  ❌ FAILED" ++
  hl

makeReport :
  Either Error (Σ (Trace (0 ⊢)) Certificate)
  → List EvalResult
  → String
makeReport r costs =
  "UPLC OPTIMIZATION: CERTIFIER REPORT"
    ++ nl
    ++ either r reportFailure (λ { (t , r) → reportPasses 1 t r costs})
```
