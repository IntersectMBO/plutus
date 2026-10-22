---
title: Conformance.Builtin.Parser.String
layout: page
---

<!-- GENERATED FILE: do not edit.
     Regenerate with `generate-agda-conformance` from the nix shell, or with
     `cabal run plutus-conformance:generate-agda-conformance` from the
     repository root. -->

Conformance tests generated from
`plutus-conformance/test-cases/uplc/evaluation/builtin/parser/string`.
See `Conformance.Eval` for how they are run.

```
module Conformance.Builtin.Parser.String where

open import Conformance.Eval
```

## string-01

```
-- builtin/parser/string/string-01
test-string-01 : Untyped
test-string-01 = (UCon (tagCon string ""))

expected-string-01 : Result
expected-string-01 = success (UCon (tagCon string ""))

_ : evalRaw test-string-01 ≡ expected-string-01
_ = refl
```

## string-02

```
-- builtin/parser/string/string-02
test-string-02 : Untyped
test-string-02 = (UCon (tagCon string "xyz"))

expected-string-02 : Result
expected-string-02 = success (UCon (tagCon string "xyz"))

_ : evalRaw test-string-02 ≡ expected-string-02
_ = refl
```

## string-03

```
-- builtin/parser/string/string-03
test-string-03 : Untyped
test-string-03 = (UCon (tagCon string "\955-calculus"))

expected-string-03 : Result
expected-string-03 = success (UCon (tagCon string "\955-calculus"))

_ : evalRaw test-string-03 ≡ expected-string-03
_ = refl
```

## string-04

```
-- builtin/parser/string/string-04
test-string-04 : Untyped
test-string-04 = (UCon (tagCon string "\t\"Success!\"\n"))

expected-string-04 : Result
expected-string-04 = success (UCon (tagCon string "\t\"Success!\"\n"))

_ : evalRaw test-string-04 ≡ expected-string-04
_ = refl
```

## string-05

```
-- builtin/parser/string/string-05
test-string-05 : Untyped
test-string-05 = (UCon (tagCon string "x \8712 \8477 \8658 x\178 \8805 0; z \8712 \8450\\\8477 \8658 z\178 \8713 {x \8712 \8477: x \8805 0}."))

expected-string-05 : Result
expected-string-05 = success (UCon (tagCon string "x \8712 \8477 \8658 x\178 \8805 0; z \8712 \8450\\\8477 \8658 z\178 \8713 {x \8712 \8477: x \8805 0}."))

_ : evalRaw test-string-05 ≡ expected-string-05
_ = refl
```

## string-06

Skipped: the program does not parse or has free variables (`parse/decode error`).

## string-07

```
-- builtin/parser/string/string-07
test-string-07 : Untyped
test-string-07 = (UCon (tagCon (list string) ("z \8712 \8477 \8658 x\178 \8805 0; z \8712 \8450" ∷ "x \8712 \8477 \8658 x\178 \8805 0; z \8712 \8450\\\8477 \8658 z\178 \8713 {x \8712 \8477: x \8805 0}." ∷ "\\" ∷ "\"" ∷ "--- \"\"\"\" \\ \\ \\\\ \\\\\\ \"" ∷ "\b\n\a\t" ∷ "\DEL" ∷ "\8364" ∷ "\n" ∷ "\t" ∷ [])))

expected-string-07 : Result
expected-string-07 = success (UCon (tagCon (list string) ("z \8712 \8477 \8658 x\178 \8805 0; z \8712 \8450" ∷ "x \8712 \8477 \8658 x\178 \8805 0; z \8712 \8450\\\8477 \8658 z\178 \8713 {x \8712 \8477: x \8805 0}." ∷ "\\" ∷ "\"" ∷ "--- \"\"\"\" \\ \\ \\\\ \\\\\\ \"" ∷ "\b\n\a\t" ∷ "\DEL" ∷ "\8364" ∷ "\n" ∷ "\t" ∷ [])))

_ : evalRaw test-string-07 ≡ expected-string-07
_ = refl
```

## string-08

Skipped: the program does not parse or has free variables (`parse/decode error`).
