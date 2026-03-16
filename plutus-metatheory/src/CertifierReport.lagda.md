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
open import Utils as U using (List; _×_; _,_; Either; either)

open import Agda.Builtin.Sigma using (Σ; _,_; snd)
open import Data.Bool using (if_then_else_)
open import Data.List as L using (List)
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

showTag : SimplifierTag → String
showTag floatDelayT = "Float Delay"
showTag forceDelayT = "Force-Delay Cancellation"
showTag forceCaseDelayT = "Float Force into Case Branches"
showTag caseOfCaseT = "Case-of-Case"
showTag caseReduceT = "Case-Constr and Case-Constant Cancellation"
showTag inlineT = "Inlining"
showTag cseT = "Common Subexpression Elimination"
showTag applyToCaseT = "Transform multi-argument applications into case-constr form"
showTag unknown = "Unknown Pass"
```

Number of times an optimization is applied on the given term in one compiler pass:

```
numSites′ : {R : Relation} {M N : 0 ⊢} → Translation R M N → ℕ
numSites′ = go 0
  where
  go : {R : Relation} {X : ℕ} {M N : X ⊢} →  ℕ → Translation R M N → ℕ
  goᵐ : {R : Relation} {X : ℕ} {M N : X ⊢} →  ℕ → TransMatch R M N → ℕ
  goᵖʷ : {R : Relation} {X : ℕ} {Ms Ns : L.List (X ⊢)} → ℕ → Pointwise (Translation R) Ms Ns → ℕ

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
  {Ms Ns : L.List (X ⊢)}
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

numSites : {M N : 0 ⊢} (tag : SimplifierTag) → RelationOf tag M N → Maybe ℕ
numSites forceDelayT p = just (numSites′ p)
numSites floatDelayT p = just (numSites′ p)
numSites cseT p = just (numSites′ p)
numSites caseReduceT p = just (numSites′ p)
numSites inlineT p = just (numSitesInline p)
numSites forceCaseDelayT _ = nothing
numSites caseOfCaseT _ = nothing
numSites applyToCaseT _ = nothing
numSites unknown _ = nothing

showSites : {M N : 0 ⊢} → (tag : SimplifierTag) → RelationOf tag M N → String
showSites t p with numSites t p
... | just n = ⇉ "Optimization sites: " ++ showℕ n
... | nothing = ""

termSize : {X : ℕ} → X ⊢ → ℕ
termSizeᵖʷ : {X : ℕ} → L.List (X ⊢) → ℕ

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

termSizeᵖʷ L.[] = 0
termSizeᵖʷ (x L.∷ xs) = termSize x + termSizeᵖʷ xs
```

Functions for producing the certifier report:

```
reportPasses :
  (n : ℕ)
  (t : Trace (0 ⊢))
  (r : Certificate t)
  → String
reportPasses _ (done _) _ = ""
reportPasses n (step tag _ x trace) (p , proofs) =
  hl ++
  "Pass " ++ showℕ n ++ ": " ++ showTag tag
    ++ (if hasRelation tag then "  ✅" else "  ⚠ (certifier unavailable)") ++
  hl ++
  (⇉ "Program Size Before: ") ++ showℕ (termSize x) ++
  nl ++
  (⇉ "Program Size After: ") ++ showℕ (termSize (head trace)) ++
  nl ++
  showSites tag p ++
  nl ++
  reportPasses (suc n) trace proofs

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
  → String
makeReport r =
  "UPLC OPTIMIZATION: CERTIFIER REPORT"
    ++ nl
    ++ either r reportFailure (λ { (t , r) → reportPasses 1 t r})
```
