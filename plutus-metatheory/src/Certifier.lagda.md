---
title: Certifier
layout: page
---

# Certifier

```
open import CertifierReport using (makeReport)
open import Untyped using (scopeCheckU0)
open import RawU using (Untyped)
open import Utils as U using (Maybe;nothing;just;Either;inj₁;inj₂;List;[];_×_;_,_)
open import VerifiedCompilation using (Cert; Trace; cert; isTrace?; traverseEitherList)
open import VerifiedCompilation.Certificate using (CertResult; Hints; inline; none; ce; proof; abort; pcePointwise; MatchOrCE; SimplifierTag)

open import Data.Bool.Base using (Bool; false; true)
open import Data.String using (String)

runCertifier : List (SimplifierTag × Hints × Untyped × Untyped) → Maybe (Cert)
runCertifier rawInput with traverseEitherList scopeCheckU0 rawInput
... | inj₁ _ = nothing
... | inj₂ inputTrace = just (cert (isTrace? inputTrace))

runCertifierMain : List (SimplifierTag × Hints × Untyped × Untyped) → Maybe (Bool × String)
runCertifierMain asts with runCertifier asts
... | just (cert r@(proof a)) = just (true , makeReport r)
... | just (cert r@(ce ¬p t b a)) = just (false , makeReport r)
... | just (cert r@(abort _ _ _)) = just (false , makeReport r)
... | nothing = nothing
{-# COMPILE GHC runCertifierMain as runCertifierMain #-}
```
