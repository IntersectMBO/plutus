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
open import Untyped
open import Utils as U using (List; _×_)

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
```

Number of times an optimization is applied on the given term in one compiler pass:

```
numSites′ : {R : Relation} {X : ℕ} {M N : X ⊢} → Translation R M N → ℕ
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

numSites : {X : ℕ} {tag : SimplifierTag} {M N : X ⊢} → Transformation tag M N → Maybe ℕ
numSites (isFD p) = just (numSites′ p)
numSites (isFlD p) = just (numSites′ p)
numSites (isCSE p) = just (numSites′ p)
numSites (isCaseReduce p) = just (numSites′ p)
-- FIXME: count number of optimization sites for inlining
numSites (isInline _) = nothing
numSites forceCaseDelayNotImplemented = nothing
numSites cocNotImplemented = nothing

showSites : {X : ℕ} {tag : SimplifierTag} {M N : X ⊢} → Transformation tag M N → String
showSites t with numSites t
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
  {X : ℕ}
  {t : U.List (SimplifierTag × Hints × (X ⊢) × (X ⊢))}
  (n : ℕ)
  (r : CertResult (Trace {X} t))
  → String
reportPasses _ (proof empty) = ""
reportPasses n (proof (cons {tag = tag} {x = x} {x' = x'} y ys)) =
  hl ++
  -- FIXME: if the certifier for a pass hasn't been implemented,
  -- it should print something like "certifier unavailable" rather than "✅".
  "Pass " ++ showℕ n ++ ": " ++ showTag tag ++ "  ✅" ++
  hl ++
  (⇉ "Program Size Before: ") ++ showℕ (termSize x) ++
  nl ++
  (⇉ "Program Size After: ") ++ showℕ (termSize x') ++
  nl ++
  showSites y ++
  nl ++
  reportPasses (suc n) (proof ys)
reportPasses n (ce _ tag _ _) =
  hl ++
  "Pass " ++ showℕ n ++ ": " ++ showTag tag ++ "  ❌ FAILED" ++
  hl
reportPasses n (abort tag _ _) =
  hl ++
  "Pass " ++ showℕ n ++ ": " ++ showTag tag ++ "  ❌ FAILED" ++
  hl

makeReport :
  {X : ℕ}
  {t : U.List (SimplifierTag × Hints × (X ⊢) × (X ⊢))}
  (r : CertResult (Trace {X} t))
  → String
makeReport r =
  "UPLC OPTIMIZATION: CERTIFIER REPORT" ++ nl ++ reportPasses 1 r
```
