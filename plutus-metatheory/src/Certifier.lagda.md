---
title: Certifier
layout: page
---

# Certifier

```
open import Function using (case_of_)
open import Data.Bool.Base using (Bool; false; true)
open import Data.String using (String)
open import Agda.Builtin.Sigma using (Σ; _,_)

open import VerifiedCompilation
open import Untyped
open import Utils
open import RawU using (Untyped)
open import VerifiedCompilation.Trace
open import VerifiedCompilation.Certificate hiding (_>>=_)
open import CertifierReport using (makeReport)

runCertifier : Dump → Either Error (Σ (Trace (0 ⊢)) Certificate)
runCertifier dump = do
  trace ← try (toTrace dump) emptyDump
  trace' ← try (checkScopeᵗ trace) illScoped
  cert ← certify trace'
  return (trace' , cert)

-- FIXME: Instead of `Maybe Bool`, we should use something like `Error` on the Haskell side
runCertifierMain : Dump → Maybe (Bool × String)
runCertifierMain dump =
  let r = runCertifier dump
  in case r of λ where
    (inj₂ (trace , p)) → just (true , makeReport r)
    (inj₁ (counterExample _)) → just (false , makeReport r)
    (inj₁ (abort _)) → just (false , makeReport r)
    (inj₁ illScoped) → nothing
    (inj₁ emptyDump) → nothing

{-# COMPILE GHC runCertifierMain as runCertifierMain #-}
```
