---
title: Conformance.Builtin.Semantics.ExpModInteger.Extra
layout: page
---

<!-- GENERATED FILE: do not edit.
     Regenerate with `cabal run plutus-conformance:generate-agda-conformance`
     from the repository root. -->

Conformance tests generated from
`plutus-conformance/test-cases/uplc/evaluation/builtin/semantics/expModInteger/extra`.
See `Conformance.Eval` for how they are run.

```
module Conformance.Builtin.Semantics.ExpModInteger.Extra where

open import Conformance.Eval
```

## expModInteger-01

```
-- builtin/semantics/expModInteger/extra/expModInteger-01
-- m < 0 -> fail
test-expModInteger-01 : Untyped
test-expModInteger-01 = (UApp (UApp (UApp (UBuiltin expModInteger) (UCon (tagCon integer (ℤ.pos 125)))) (UCon (tagCon integer (ℤ.negsuc 83240)))) (UCon (tagCon integer (ℤ.negsuc 6))))

expected-expModInteger-01 : Result
expected-expModInteger-01 = failure

-- Pending: postulated builtin `expModInteger`.
pending-expModInteger-01 : Set
pending-expModInteger-01 = Pending (evalRaw test-expModInteger-01 ≡ expected-expModInteger-01)
```

## expModInteger-02

```
-- builtin/semantics/expModInteger/extra/expModInteger-02
-- m < 0 -> fail
test-expModInteger-02 : Untyped
test-expModInteger-02 = (UApp (UApp (UApp (UBuiltin expModInteger) (UCon (tagCon integer (ℤ.negsuc 884)))) (UCon (tagCon integer (ℤ.pos 5000000)))) (UCon (tagCon integer (ℤ.negsuc 1))))

expected-expModInteger-02 : Result
expected-expModInteger-02 = failure

-- Pending: postulated builtin `expModInteger`.
pending-expModInteger-02 : Set
pending-expModInteger-02 = Pending (evalRaw test-expModInteger-02 ≡ expected-expModInteger-02)
```

## expModInteger-03

```
-- builtin/semantics/expModInteger/extra/expModInteger-03
-- m < 0 -> fail
test-expModInteger-03 : Untyped
test-expModInteger-03 = (UApp (UApp (UApp (UBuiltin expModInteger) (UCon (tagCon integer (ℤ.pos 79123789)))) (UCon (tagCon integer (ℤ.pos 34767237)))) (UCon (tagCon integer (ℤ.negsuc 99572135136512635615235151))))

expected-expModInteger-03 : Result
expected-expModInteger-03 = failure

-- Pending: postulated builtin `expModInteger`.
pending-expModInteger-03 : Set
pending-expModInteger-03 = Pending (evalRaw test-expModInteger-03 ≡ expected-expModInteger-03)
```

## expModInteger-04

```
-- builtin/semantics/expModInteger/extra/expModInteger-04
-- m = 0 -> fail
test-expModInteger-04 : Untyped
test-expModInteger-04 = (UApp (UApp (UApp (UBuiltin expModInteger) (UCon (tagCon integer (ℤ.pos 0)))) (UCon (tagCon integer (ℤ.pos 0)))) (UCon (tagCon integer (ℤ.negsuc 0))))

expected-expModInteger-04 : Result
expected-expModInteger-04 = failure

-- Pending: postulated builtin `expModInteger`.
pending-expModInteger-04 : Set
pending-expModInteger-04 = Pending (evalRaw test-expModInteger-04 ≡ expected-expModInteger-04)
```

## expModInteger-05

```
-- builtin/semantics/expModInteger/extra/expModInteger-05
-- m = 0 -> fail
test-expModInteger-05 : Untyped
test-expModInteger-05 = (UApp (UApp (UApp (UBuiltin expModInteger) (UCon (tagCon integer (ℤ.pos 0)))) (UCon (tagCon integer (ℤ.pos 0)))) (UCon (tagCon integer (ℤ.pos 0))))

expected-expModInteger-05 : Result
expected-expModInteger-05 = failure

-- Pending: postulated builtin `expModInteger`.
pending-expModInteger-05 : Set
pending-expModInteger-05 = Pending (evalRaw test-expModInteger-05 ≡ expected-expModInteger-05)
```

## expModInteger-06

```
-- builtin/semantics/expModInteger/extra/expModInteger-06
-- m = 0 -> fail
test-expModInteger-06 : Untyped
test-expModInteger-06 = (UApp (UApp (UApp (UBuiltin expModInteger) (UCon (tagCon integer (ℤ.pos 5)))) (UCon (tagCon integer (ℤ.pos 12)))) (UCon (tagCon integer (ℤ.pos 0))))

expected-expModInteger-06 : Result
expected-expModInteger-06 = failure

-- Pending: postulated builtin `expModInteger`.
pending-expModInteger-06 : Set
pending-expModInteger-06 = Pending (evalRaw test-expModInteger-06 ≡ expected-expModInteger-06)
```

## expModInteger-07

```
-- builtin/semantics/expModInteger/extra/expModInteger-07
-- m = 0 -> fail
test-expModInteger-07 : Untyped
test-expModInteger-07 = (UApp (UApp (UApp (UBuiltin expModInteger) (UCon (tagCon integer (ℤ.pos 123234725734785273457322)))) (UCon (tagCon integer (ℤ.pos 321)))) (UCon (tagCon integer (ℤ.pos 0))))

expected-expModInteger-07 : Result
expected-expModInteger-07 = failure

-- Pending: postulated builtin `expModInteger`.
pending-expModInteger-07 : Set
pending-expModInteger-07 = Pending (evalRaw test-expModInteger-07 ≡ expected-expModInteger-07)
```

## expModInteger-08

```
-- builtin/semantics/expModInteger/extra/expModInteger-08
-- m = 1 -> return 0
test-expModInteger-08 : Untyped
test-expModInteger-08 = (UApp (UApp (UApp (UBuiltin expModInteger) (UCon (tagCon integer (ℤ.pos 101)))) (UCon (tagCon integer (ℤ.pos 99)))) (UCon (tagCon integer (ℤ.pos 1))))

expected-expModInteger-08 : Result
expected-expModInteger-08 = success (UCon (tagCon integer (ℤ.pos 0)))

-- Pending: postulated builtin `expModInteger`.
pending-expModInteger-08 : Set
pending-expModInteger-08 = Pending (evalRaw test-expModInteger-08 ≡ expected-expModInteger-08)
```

## expModInteger-09

```
-- builtin/semantics/expModInteger/extra/expModInteger-09
-- m = 1 -> return 0
test-expModInteger-09 : Untyped
test-expModInteger-09 = (UApp (UApp (UApp (UBuiltin expModInteger) (UCon (tagCon integer (ℤ.pos 12389)))) (UCon (tagCon integer (ℤ.negsuc 8)))) (UCon (tagCon integer (ℤ.pos 1))))

expected-expModInteger-09 : Result
expected-expModInteger-09 = success (UCon (tagCon integer (ℤ.pos 0)))

-- Pending: postulated builtin `expModInteger`.
pending-expModInteger-09 : Set
pending-expModInteger-09 = Pending (evalRaw test-expModInteger-09 ≡ expected-expModInteger-09)
```

## expModInteger-10

```
-- builtin/semantics/expModInteger/extra/expModInteger-10
-- m = 1 -> return 0
test-expModInteger-10 : Untyped
test-expModInteger-10 = (UApp (UApp (UApp (UBuiltin expModInteger) (UCon (tagCon integer (ℤ.negsuc 8987923471283646712347891237947623467283)))) (UCon (tagCon integer (ℤ.pos 0)))) (UCon (tagCon integer (ℤ.pos 1))))

expected-expModInteger-10 : Result
expected-expModInteger-10 = success (UCon (tagCon integer (ℤ.pos 0)))

-- Pending: postulated builtin `expModInteger`.
pending-expModInteger-10 : Set
pending-expModInteger-10 = Pending (evalRaw test-expModInteger-10 ≡ expected-expModInteger-10)
```

## expModInteger-11

```
-- builtin/semantics/expModInteger/extra/expModInteger-11
-- m = 1 -> return 0
test-expModInteger-11 : Untyped
test-expModInteger-11 = (UApp (UApp (UApp (UBuiltin expModInteger) (UCon (tagCon integer (ℤ.pos 0)))) (UCon (tagCon integer (ℤ.pos 9)))) (UCon (tagCon integer (ℤ.pos 1))))

expected-expModInteger-11 : Result
expected-expModInteger-11 = success (UCon (tagCon integer (ℤ.pos 0)))

-- Pending: postulated builtin `expModInteger`.
pending-expModInteger-11 : Set
pending-expModInteger-11 = Pending (evalRaw test-expModInteger-11 ≡ expected-expModInteger-11)
```

## expModInteger-12

```
-- builtin/semantics/expModInteger/extra/expModInteger-12
-- m = 1 -> return 0
test-expModInteger-12 : Untyped
test-expModInteger-12 = (UApp (UApp (UApp (UBuiltin expModInteger) (UCon (tagCon integer (ℤ.pos 9)))) (UCon (tagCon integer (ℤ.pos 0)))) (UCon (tagCon integer (ℤ.pos 1))))

expected-expModInteger-12 : Result
expected-expModInteger-12 = success (UCon (tagCon integer (ℤ.pos 0)))

-- Pending: postulated builtin `expModInteger`.
pending-expModInteger-12 : Set
pending-expModInteger-12 = Pending (evalRaw test-expModInteger-12 ≡ expected-expModInteger-12)
```

## expModInteger-13

```
-- builtin/semantics/expModInteger/extra/expModInteger-13
-- m = 1 -> return 0
test-expModInteger-13 : Untyped
test-expModInteger-13 = (UApp (UApp (UApp (UBuiltin expModInteger) (UCon (tagCon integer (ℤ.pos 0)))) (UCon (tagCon integer (ℤ.pos 0)))) (UCon (tagCon integer (ℤ.pos 1))))

expected-expModInteger-13 : Result
expected-expModInteger-13 = success (UCon (tagCon integer (ℤ.pos 0)))

-- Pending: postulated builtin `expModInteger`.
pending-expModInteger-13 : Set
pending-expModInteger-13 = Pending (evalRaw test-expModInteger-13 ≡ expected-expModInteger-13)
```

## expModInteger-14

```
-- builtin/semantics/expModInteger/extra/expModInteger-14
-- m > 1 and e = 0 -> return 1
test-expModInteger-14 : Untyped
test-expModInteger-14 = (UApp (UApp (UApp (UBuiltin expModInteger) (UCon (tagCon integer (ℤ.negsuc 788)))) (UCon (tagCon integer (ℤ.pos 0)))) (UCon (tagCon integer (ℤ.pos 123))))

expected-expModInteger-14 : Result
expected-expModInteger-14 = success (UCon (tagCon integer (ℤ.pos 1)))

-- Pending: postulated builtin `expModInteger`.
pending-expModInteger-14 : Set
pending-expModInteger-14 = Pending (evalRaw test-expModInteger-14 ≡ expected-expModInteger-14)
```

## expModInteger-15

```
-- builtin/semantics/expModInteger/extra/expModInteger-15
-- m > 1 and e = 0 -> return 1
test-expModInteger-15 : Untyped
test-expModInteger-15 = (UApp (UApp (UApp (UBuiltin expModInteger) (UCon (tagCon integer (ℤ.pos 7)))) (UCon (tagCon integer (ℤ.pos 0)))) (UCon (tagCon integer (ℤ.pos 11))))

expected-expModInteger-15 : Result
expected-expModInteger-15 = success (UCon (tagCon integer (ℤ.pos 1)))

-- Pending: postulated builtin `expModInteger`.
pending-expModInteger-15 : Set
pending-expModInteger-15 = Pending (evalRaw test-expModInteger-15 ≡ expected-expModInteger-15)
```

## expModInteger-16

```
-- builtin/semantics/expModInteger/extra/expModInteger-16
-- m > 1 and e = 0 -> return 1
test-expModInteger-16 : Untyped
test-expModInteger-16 = (UApp (UApp (UApp (UBuiltin expModInteger) (UCon (tagCon integer (ℤ.pos 6716724038975293475892345238945892345)))) (UCon (tagCon integer (ℤ.pos 0)))) (UCon (tagCon integer (ℤ.pos 11))))

expected-expModInteger-16 : Result
expected-expModInteger-16 = success (UCon (tagCon integer (ℤ.pos 1)))

-- Pending: postulated builtin `expModInteger`.
pending-expModInteger-16 : Set
pending-expModInteger-16 = Pending (evalRaw test-expModInteger-16 ≡ expected-expModInteger-16)
```

## expModInteger-17

```
-- builtin/semantics/expModInteger/extra/expModInteger-17
-- m > 1 and e = 0 -> return 1
test-expModInteger-17 : Untyped
test-expModInteger-17 = (UApp (UApp (UApp (UBuiltin expModInteger) (UCon (tagCon integer (ℤ.pos 6716724038975293475892345238945892345)))) (UCon (tagCon integer (ℤ.pos 0)))) (UCon (tagCon integer (ℤ.pos 11000000000000000000000000000001200000000000000000000893))))

expected-expModInteger-17 : Result
expected-expModInteger-17 = success (UCon (tagCon integer (ℤ.pos 1)))

-- Pending: postulated builtin `expModInteger`.
pending-expModInteger-17 : Set
pending-expModInteger-17 = Pending (evalRaw test-expModInteger-17 ≡ expected-expModInteger-17)
```

## expModInteger-18

```
-- builtin/semantics/expModInteger/extra/expModInteger-18
-- m > 1 and e = 0 -> return 1
test-expModInteger-18 : Untyped
test-expModInteger-18 = (UApp (UApp (UApp (UBuiltin expModInteger) (UCon (tagCon integer (ℤ.pos 0)))) (UCon (tagCon integer (ℤ.pos 0)))) (UCon (tagCon integer (ℤ.pos 2123478956273846578234523475237))))

expected-expModInteger-18 : Result
expected-expModInteger-18 = success (UCon (tagCon integer (ℤ.pos 1)))

-- Pending: postulated builtin `expModInteger`.
pending-expModInteger-18 : Set
pending-expModInteger-18 = Pending (evalRaw test-expModInteger-18 ≡ expected-expModInteger-18)
```

## expModInteger-19

```
-- builtin/semantics/expModInteger/extra/expModInteger-19
-- m > 1, e = 1 -> return b modulo m
test-expModInteger-19 : Untyped
test-expModInteger-19 = (UApp (UApp (UBuiltin equalsInteger) (UApp (UApp (UApp (UBuiltin expModInteger) (UCon (tagCon integer (ℤ.pos 117)))) (UCon (tagCon integer (ℤ.pos 1)))) (UCon (tagCon integer (ℤ.pos 1000))))) (UApp (UApp (UBuiltin modInteger) (UCon (tagCon integer (ℤ.pos 117)))) (UCon (tagCon integer (ℤ.pos 1000)))))

expected-expModInteger-19 : Result
expected-expModInteger-19 = success (UCon (tagCon bool true))

-- Pending: postulated builtin `expModInteger`.
pending-expModInteger-19 : Set
pending-expModInteger-19 = Pending (evalRaw test-expModInteger-19 ≡ expected-expModInteger-19)
```

## expModInteger-20

```
-- builtin/semantics/expModInteger/extra/expModInteger-20
-- m > 1, e = 1 -> return b modulo m
test-expModInteger-20 : Untyped
test-expModInteger-20 = (UApp (UApp (UBuiltin equalsInteger) (UApp (UApp (UApp (UBuiltin expModInteger) (UCon (tagCon integer (ℤ.pos 4123213117)))) (UCon (tagCon integer (ℤ.pos 1)))) (UCon (tagCon integer (ℤ.pos 1000))))) (UApp (UApp (UBuiltin modInteger) (UCon (tagCon integer (ℤ.pos 4123213117)))) (UCon (tagCon integer (ℤ.pos 1000)))))

expected-expModInteger-20 : Result
expected-expModInteger-20 = success (UCon (tagCon bool true))

-- Pending: postulated builtin `expModInteger`.
pending-expModInteger-20 : Set
pending-expModInteger-20 = Pending (evalRaw test-expModInteger-20 ≡ expected-expModInteger-20)
```

## expModInteger-21

```
-- builtin/semantics/expModInteger/extra/expModInteger-21
-- m > 1, e = 1 -> return b modulo m
test-expModInteger-21 : Untyped
test-expModInteger-21 = (UApp (UApp (UBuiltin equalsInteger) (UApp (UApp (UApp (UBuiltin expModInteger) (UCon (tagCon integer (ℤ.negsuc 882)))) (UCon (tagCon integer (ℤ.pos 1)))) (UCon (tagCon integer (ℤ.pos 1000))))) (UApp (UApp (UBuiltin modInteger) (UCon (tagCon integer (ℤ.negsuc 882)))) (UCon (tagCon integer (ℤ.pos 1000)))))

expected-expModInteger-21 : Result
expected-expModInteger-21 = success (UCon (tagCon bool true))

-- Pending: postulated builtin `expModInteger`.
pending-expModInteger-21 : Set
pending-expModInteger-21 = Pending (evalRaw test-expModInteger-21 ≡ expected-expModInteger-21)
```

## expModInteger-22

```
-- builtin/semantics/expModInteger/extra/expModInteger-22
-- m > 1, e = 1 -> return b modulo m
test-expModInteger-22 : Untyped
test-expModInteger-22 = (UApp (UApp (UBuiltin equalsInteger) (UApp (UApp (UApp (UBuiltin expModInteger) (UCon (tagCon integer (ℤ.negsuc 10000000000000000000000000882)))) (UCon (tagCon integer (ℤ.pos 1)))) (UCon (tagCon integer (ℤ.pos 1000))))) (UApp (UApp (UBuiltin modInteger) (UCon (tagCon integer (ℤ.negsuc 10000000000000000000000000882)))) (UCon (tagCon integer (ℤ.pos 1000)))))

expected-expModInteger-22 : Result
expected-expModInteger-22 = success (UCon (tagCon bool true))

-- Pending: postulated builtin `expModInteger`.
pending-expModInteger-22 : Set
pending-expModInteger-22 = Pending (evalRaw test-expModInteger-22 ≡ expected-expModInteger-22)
```

## expModInteger-23

```
-- builtin/semantics/expModInteger/extra/expModInteger-23
-- m > 1, e = 1 -> return b modulo m
test-expModInteger-23 : Untyped
test-expModInteger-23 = (UApp (UApp (UBuiltin equalsInteger) (UApp (UApp (UApp (UBuiltin expModInteger) (UCon (tagCon integer (ℤ.pos 0)))) (UCon (tagCon integer (ℤ.pos 1)))) (UCon (tagCon integer (ℤ.pos 123321))))) (UApp (UApp (UBuiltin modInteger) (UCon (tagCon integer (ℤ.pos 0)))) (UCon (tagCon integer (ℤ.pos 123321)))))

expected-expModInteger-23 : Result
expected-expModInteger-23 = success (UCon (tagCon bool true))

-- Pending: postulated builtin `expModInteger`.
pending-expModInteger-23 : Set
pending-expModInteger-23 = Pending (evalRaw test-expModInteger-23 ≡ expected-expModInteger-23)
```

## expModInteger-24

```
-- builtin/semantics/expModInteger/extra/expModInteger-24
-- m > 1, e = 1 -> return b modulo m
test-expModInteger-24 : Untyped
test-expModInteger-24 = (UApp (UApp (UBuiltin equalsInteger) (UApp (UApp (UApp (UBuiltin expModInteger) (UCon (tagCon integer (ℤ.pos 123321123321)))) (UCon (tagCon integer (ℤ.pos 1)))) (UCon (tagCon integer (ℤ.pos 123321))))) (UApp (UApp (UBuiltin modInteger) (UCon (tagCon integer (ℤ.pos 123321123321)))) (UCon (tagCon integer (ℤ.pos 123321)))))

expected-expModInteger-24 : Result
expected-expModInteger-24 = success (UCon (tagCon bool true))

-- Pending: postulated builtin `expModInteger`.
pending-expModInteger-24 : Set
pending-expModInteger-24 = Pending (evalRaw test-expModInteger-24 ≡ expected-expModInteger-24)
```

## expModInteger-25

```
-- builtin/semantics/expModInteger/extra/expModInteger-25
-- m > 1, e = 1 -> return b modulo m
test-expModInteger-25 : Untyped
test-expModInteger-25 = (UApp (UApp (UBuiltin equalsInteger) (UApp (UApp (UApp (UBuiltin expModInteger) (UCon (tagCon integer (ℤ.pos 71893478901378904789123789401789034781278399999)))) (UCon (tagCon integer (ℤ.pos 1)))) (UCon (tagCon integer (ℤ.pos 1789345724789527834523495789345))))) (UApp (UApp (UBuiltin modInteger) (UCon (tagCon integer (ℤ.pos 71893478901378904789123789401789034781278399999)))) (UCon (tagCon integer (ℤ.pos 1789345724789527834523495789345)))))

expected-expModInteger-25 : Result
expected-expModInteger-25 = success (UCon (tagCon bool true))

-- Pending: postulated builtin `expModInteger`.
pending-expModInteger-25 : Set
pending-expModInteger-25 = Pending (evalRaw test-expModInteger-25 ≡ expected-expModInteger-25)
```

## expModInteger-26

```
-- builtin/semantics/expModInteger/extra/expModInteger-26
-- m > 1, e = -1, gcd a m > 1 -> fail
test-expModInteger-26 : Untyped
test-expModInteger-26 = (UApp (UApp (UApp (UBuiltin expModInteger) (UCon (tagCon integer (ℤ.pos 0)))) (UCon (tagCon integer (ℤ.negsuc 0)))) (UCon (tagCon integer (ℤ.pos 17))))

expected-expModInteger-26 : Result
expected-expModInteger-26 = failure

-- Pending: postulated builtin `expModInteger`.
pending-expModInteger-26 : Set
pending-expModInteger-26 = Pending (evalRaw test-expModInteger-26 ≡ expected-expModInteger-26)
```

## expModInteger-27

```
-- builtin/semantics/expModInteger/extra/expModInteger-27
-- m > 1, e = -1, gcd a m > 1 -> fail
test-expModInteger-27 : Untyped
test-expModInteger-27 = (UApp (UApp (UApp (UBuiltin expModInteger) (UCon (tagCon integer (ℤ.pos 17)))) (UCon (tagCon integer (ℤ.negsuc 0)))) (UCon (tagCon integer (ℤ.pos 17))))

expected-expModInteger-27 : Result
expected-expModInteger-27 = failure

-- Pending: postulated builtin `expModInteger`.
pending-expModInteger-27 : Set
pending-expModInteger-27 = Pending (evalRaw test-expModInteger-27 ≡ expected-expModInteger-27)
```

## expModInteger-28

```
-- builtin/semantics/expModInteger/extra/expModInteger-28
-- m > 1, e = -1, gcd a m > 1 -> fail
test-expModInteger-28 : Untyped
test-expModInteger-28 = (UApp (UApp (UApp (UBuiltin expModInteger) (UCon (tagCon integer (ℤ.negsuc 1716)))) (UCon (tagCon integer (ℤ.negsuc 0)))) (UCon (tagCon integer (ℤ.pos 17))))

expected-expModInteger-28 : Result
expected-expModInteger-28 = failure

-- Pending: postulated builtin `expModInteger`.
pending-expModInteger-28 : Set
pending-expModInteger-28 = Pending (evalRaw test-expModInteger-28 ≡ expected-expModInteger-28)
```

## expModInteger-29

```
-- builtin/semantics/expModInteger/extra/expModInteger-29
-- m = 3842610773*16548071329, e = -1, gcd a m > 1 -> fail
test-expModInteger-29 : Untyped
test-expModInteger-29 = (UApp (UApp (UApp (UBuiltin expModInteger) (UCon (tagCon integer (ℤ.pos 3842610773)))) (UCon (tagCon integer (ℤ.negsuc 0)))) (UCon (tagCon integer (ℤ.pos 63587797161187827317))))

expected-expModInteger-29 : Result
expected-expModInteger-29 = failure

-- Pending: postulated builtin `expModInteger`.
pending-expModInteger-29 : Set
pending-expModInteger-29 = Pending (evalRaw test-expModInteger-29 ≡ expected-expModInteger-29)
```

## expModInteger-30

```
-- builtin/semantics/expModInteger/extra/expModInteger-30
-- m = 3842610773*16548071329, e = -1, gcd a m > 1 -> fail
test-expModInteger-30 : Untyped
test-expModInteger-30 = (UApp (UApp (UApp (UBuiltin expModInteger) (UCon (tagCon integer (ℤ.pos 16548071329)))) (UCon (tagCon integer (ℤ.negsuc 0)))) (UCon (tagCon integer (ℤ.pos 63587797161187827317))))

expected-expModInteger-30 : Result
expected-expModInteger-30 = failure

-- Pending: postulated builtin `expModInteger`.
pending-expModInteger-30 : Set
pending-expModInteger-30 = Pending (evalRaw test-expModInteger-30 ≡ expected-expModInteger-30)
```

## expModInteger-31

```
-- builtin/semantics/expModInteger/extra/expModInteger-31
-- m > 1, e < 0, gcd a m > 1 -> fail
test-expModInteger-31 : Untyped
test-expModInteger-31 = (UApp (UApp (UApp (UBuiltin expModInteger) (UCon (tagCon integer (ℤ.pos 0)))) (UCon (tagCon integer (ℤ.negsuc 1134134120)))) (UCon (tagCon integer (ℤ.pos 17))))

expected-expModInteger-31 : Result
expected-expModInteger-31 = failure

-- Pending: postulated builtin `expModInteger`.
pending-expModInteger-31 : Set
pending-expModInteger-31 = Pending (evalRaw test-expModInteger-31 ≡ expected-expModInteger-31)
```

## expModInteger-32

```
-- builtin/semantics/expModInteger/extra/expModInteger-32
-- m > 1, e < 0, gcd a m > 1 -> fail
test-expModInteger-32 : Untyped
test-expModInteger-32 = (UApp (UApp (UApp (UBuiltin expModInteger) (UCon (tagCon integer (ℤ.pos 17)))) (UCon (tagCon integer (ℤ.negsuc 4)))) (UCon (tagCon integer (ℤ.pos 17))))

expected-expModInteger-32 : Result
expected-expModInteger-32 = failure

-- Pending: postulated builtin `expModInteger`.
pending-expModInteger-32 : Set
pending-expModInteger-32 = Pending (evalRaw test-expModInteger-32 ≡ expected-expModInteger-32)
```

## expModInteger-33

```
-- builtin/semantics/expModInteger/extra/expModInteger-33
-- m > 1, e < 0, gcd a m > 1 -> fail
test-expModInteger-33 : Untyped
test-expModInteger-33 = (UApp (UApp (UApp (UBuiltin expModInteger) (UCon (tagCon integer (ℤ.negsuc 1716)))) (UCon (tagCon integer (ℤ.negsuc 999999999999999999999999999999)))) (UCon (tagCon integer (ℤ.pos 17))))

expected-expModInteger-33 : Result
expected-expModInteger-33 = failure

-- Pending: postulated builtin `expModInteger`.
pending-expModInteger-33 : Set
pending-expModInteger-33 = Pending (evalRaw test-expModInteger-33 ≡ expected-expModInteger-33)
```

## expModInteger-34

```
-- builtin/semantics/expModInteger/extra/expModInteger-34
-- m = 3842610773*16548071329, e < 0, gcd a m > 1 -> fail
test-expModInteger-34 : Untyped
test-expModInteger-34 = (UApp (UApp (UApp (UBuiltin expModInteger) (UCon (tagCon integer (ℤ.pos 3842610773)))) (UCon (tagCon integer (ℤ.negsuc 777777777777777777777770)))) (UCon (tagCon integer (ℤ.pos 63587797161187827317))))

expected-expModInteger-34 : Result
expected-expModInteger-34 = failure

-- Pending: postulated builtin `expModInteger`.
pending-expModInteger-34 : Set
pending-expModInteger-34 = Pending (evalRaw test-expModInteger-34 ≡ expected-expModInteger-34)
```

## expModInteger-35

```
-- builtin/semantics/expModInteger/extra/expModInteger-35
-- m = 3842610773*16548071329, e < 0, gcd a m > 1 -> fail
test-expModInteger-35 : Untyped
test-expModInteger-35 = (UApp (UApp (UApp (UBuiltin expModInteger) (UCon (tagCon integer (ℤ.pos 16548071329)))) (UCon (tagCon integer (ℤ.negsuc 18446744073709551615)))) (UCon (tagCon integer (ℤ.pos 63587797161187827317))))

expected-expModInteger-35 : Result
expected-expModInteger-35 = failure

-- Pending: postulated builtin `expModInteger`.
pending-expModInteger-35 : Set
pending-expModInteger-35 = Pending (evalRaw test-expModInteger-35 ≡ expected-expModInteger-35)
```

## expModInteger-36

```
-- builtin/semantics/expModInteger/extra/expModInteger-36
-- m > 1, e = -1, gcd a m = 1 -> succeed
test-expModInteger-36 : Untyped
test-expModInteger-36 = (UApp (UApp (UApp (UBuiltin expModInteger) (UCon (tagCon integer (ℤ.pos 1)))) (UCon (tagCon integer (ℤ.negsuc 0)))) (UCon (tagCon integer (ℤ.pos 17))))

expected-expModInteger-36 : Result
expected-expModInteger-36 = success (UCon (tagCon integer (ℤ.pos 1)))

-- Pending: postulated builtin `expModInteger`.
pending-expModInteger-36 : Set
pending-expModInteger-36 = Pending (evalRaw test-expModInteger-36 ≡ expected-expModInteger-36)
```

## expModInteger-37

```
-- builtin/semantics/expModInteger/extra/expModInteger-37
-- m > 1, e = -1, gcd a m = 1 -> succeed
test-expModInteger-37 : Untyped
test-expModInteger-37 = (UApp (UApp (UApp (UBuiltin expModInteger) (UCon (tagCon integer (ℤ.pos 18)))) (UCon (tagCon integer (ℤ.negsuc 0)))) (UCon (tagCon integer (ℤ.pos 17))))

expected-expModInteger-37 : Result
expected-expModInteger-37 = success (UCon (tagCon integer (ℤ.pos 1)))

-- Pending: postulated builtin `expModInteger`.
pending-expModInteger-37 : Set
pending-expModInteger-37 = Pending (evalRaw test-expModInteger-37 ≡ expected-expModInteger-37)
```

## expModInteger-38

```
-- builtin/semantics/expModInteger/extra/expModInteger-38
-- m > 1, e = -1, gcd a m = 1 -> succeed
test-expModInteger-38 : Untyped
test-expModInteger-38 = (UApp (UApp (UApp (UBuiltin expModInteger) (UCon (tagCon integer (ℤ.negsuc 1718)))) (UCon (tagCon integer (ℤ.negsuc 0)))) (UCon (tagCon integer (ℤ.pos 17))))

expected-expModInteger-38 : Result
expected-expModInteger-38 = success (UCon (tagCon integer (ℤ.pos 8)))

-- Pending: postulated builtin `expModInteger`.
pending-expModInteger-38 : Set
pending-expModInteger-38 = Pending (evalRaw test-expModInteger-38 ≡ expected-expModInteger-38)
```

## expModInteger-39

```
-- builtin/semantics/expModInteger/extra/expModInteger-39
-- m = 3842610773*16548071329, e = -1, gcd a m = 1 -> succeed
test-expModInteger-39 : Untyped
test-expModInteger-39 = (UApp (UApp (UApp (UBuiltin expModInteger) (UCon (tagCon integer (ℤ.pos 3842610771)))) (UCon (tagCon integer (ℤ.negsuc 0)))) (UCon (tagCon integer (ℤ.pos 63587797161187827317))))

expected-expModInteger-39 : Result
expected-expModInteger-39 = success (UCon (tagCon integer (ℤ.pos 46828242895014337770)))

-- Pending: postulated builtin `expModInteger`.
pending-expModInteger-39 : Set
pending-expModInteger-39 = Pending (evalRaw test-expModInteger-39 ≡ expected-expModInteger-39)
```

## expModInteger-40

```
-- builtin/semantics/expModInteger/extra/expModInteger-40
-- m = 3842610773*16548071329, e = -1, gcd a m = 1 -> succeed
test-expModInteger-40 : Untyped
test-expModInteger-40 = (UApp (UApp (UApp (UBuiltin expModInteger) (UCon (tagCon integer (ℤ.pos 1654807132907)))) (UCon (tagCon integer (ℤ.negsuc 0)))) (UCon (tagCon integer (ℤ.pos 63587797161187827317))))

expected-expModInteger-40 : Result
expected-expModInteger-40 = success (UCon (tagCon integer (ℤ.pos 36516505836773408443)))

-- Pending: postulated builtin `expModInteger`.
pending-expModInteger-40 : Set
pending-expModInteger-40 = Pending (evalRaw test-expModInteger-40 ≡ expected-expModInteger-40)
```

## expModInteger-41

```
-- builtin/semantics/expModInteger/extra/expModInteger-41
-- m > 1, e < 0, gcd a m = 1 -> succeed
test-expModInteger-41 : Untyped
test-expModInteger-41 = (UApp (UApp (UApp (UBuiltin expModInteger) (UCon (tagCon integer (ℤ.pos 1)))) (UCon (tagCon integer (ℤ.negsuc 1134134120)))) (UCon (tagCon integer (ℤ.pos 17))))

expected-expModInteger-41 : Result
expected-expModInteger-41 = success (UCon (tagCon integer (ℤ.pos 1)))

-- Pending: postulated builtin `expModInteger`.
pending-expModInteger-41 : Set
pending-expModInteger-41 = Pending (evalRaw test-expModInteger-41 ≡ expected-expModInteger-41)
```

## expModInteger-42

```
-- builtin/semantics/expModInteger/extra/expModInteger-42
-- m > 1, e < 0, gcd a m = 1 -> succeed
test-expModInteger-42 : Untyped
test-expModInteger-42 = (UApp (UApp (UApp (UBuiltin expModInteger) (UCon (tagCon integer (ℤ.pos 18)))) (UCon (tagCon integer (ℤ.negsuc 4)))) (UCon (tagCon integer (ℤ.pos 17))))

expected-expModInteger-42 : Result
expected-expModInteger-42 = success (UCon (tagCon integer (ℤ.pos 1)))

-- Pending: postulated builtin `expModInteger`.
pending-expModInteger-42 : Set
pending-expModInteger-42 = Pending (evalRaw test-expModInteger-42 ≡ expected-expModInteger-42)
```

## expModInteger-43

```
-- builtin/semantics/expModInteger/extra/expModInteger-43
-- m > 1, e < 0, gcd a m = 1 -> succeed
test-expModInteger-43 : Untyped
test-expModInteger-43 = (UApp (UApp (UApp (UBuiltin expModInteger) (UCon (tagCon integer (ℤ.negsuc 1718)))) (UCon (tagCon integer (ℤ.negsuc 100000000000000000000000000000006)))) (UCon (tagCon integer (ℤ.pos 17))))

expected-expModInteger-43 : Result
expected-expModInteger-43 = success (UCon (tagCon integer (ℤ.pos 15)))

-- Pending: postulated builtin `expModInteger`.
pending-expModInteger-43 : Set
pending-expModInteger-43 = Pending (evalRaw test-expModInteger-43 ≡ expected-expModInteger-43)
```

## expModInteger-44

```
-- builtin/semantics/expModInteger/extra/expModInteger-44
-- m = 3842610773*16548071329, e < 0, gcd a m = 1 -> succeed
test-expModInteger-44 : Untyped
test-expModInteger-44 = (UApp (UApp (UApp (UBuiltin expModInteger) (UCon (tagCon integer (ℤ.pos 3842610771)))) (UCon (tagCon integer (ℤ.negsuc 777777777777777777777770)))) (UCon (tagCon integer (ℤ.pos 63587797161187827317))))

expected-expModInteger-44 : Result
expected-expModInteger-44 = success (UCon (tagCon integer (ℤ.pos 57441510316368658593)))

-- Pending: postulated builtin `expModInteger`.
pending-expModInteger-44 : Set
pending-expModInteger-44 = Pending (evalRaw test-expModInteger-44 ≡ expected-expModInteger-44)
```

## expModInteger-45

```
-- builtin/semantics/expModInteger/extra/expModInteger-45
-- m = 3842610773*16548071329, e < 0, gcd a m = 1 -> succeed
test-expModInteger-45 : Untyped
test-expModInteger-45 = (UApp (UApp (UApp (UBuiltin expModInteger) (UCon (tagCon integer (ℤ.pos 1654807132907)))) (UCon (tagCon integer (ℤ.negsuc 18446744073709551615)))) (UCon (tagCon integer (ℤ.pos 63587797161187827317))))

expected-expModInteger-45 : Result
expected-expModInteger-45 = success (UCon (tagCon integer (ℤ.pos 60415552098464659702)))

-- Pending: postulated builtin `expModInteger`.
pending-expModInteger-45 : Set
pending-expModInteger-45 = Pending (evalRaw test-expModInteger-45 ≡ expected-expModInteger-45)
```

## expModInteger-46

```
-- builtin/semantics/expModInteger/extra/expModInteger-46
-- m > 1, e = -1, gcd a m = 1 -> compute inverse
test-expModInteger-46 : Untyped
test-expModInteger-46 = (UApp (UApp (UBuiltin equalsInteger) (UApp (UApp (UBuiltin modInteger) (UApp (UApp (UBuiltin multiplyInteger) (UApp (UApp (UApp (UBuiltin expModInteger) (UCon (tagCon integer (ℤ.pos 1)))) (UCon (tagCon integer (ℤ.negsuc 0)))) (UCon (tagCon integer (ℤ.pos 17))))) (UApp (UApp (UApp (UBuiltin expModInteger) (UCon (tagCon integer (ℤ.pos 1)))) (UCon (tagCon integer (ℤ.pos 1)))) (UCon (tagCon integer (ℤ.pos 17)))))) (UCon (tagCon integer (ℤ.pos 17))))) (UCon (tagCon integer (ℤ.pos 1))))

expected-expModInteger-46 : Result
expected-expModInteger-46 = success (UCon (tagCon bool true))

-- Pending: postulated builtin `expModInteger`.
pending-expModInteger-46 : Set
pending-expModInteger-46 = Pending (evalRaw test-expModInteger-46 ≡ expected-expModInteger-46)
```

## expModInteger-47

```
-- builtin/semantics/expModInteger/extra/expModInteger-47
-- m > 1, e = -1, gcd a m = 1 -> compute inverse
test-expModInteger-47 : Untyped
test-expModInteger-47 = (UApp (UApp (UBuiltin equalsInteger) (UApp (UApp (UBuiltin modInteger) (UApp (UApp (UBuiltin multiplyInteger) (UApp (UApp (UApp (UBuiltin expModInteger) (UCon (tagCon integer (ℤ.pos 18)))) (UCon (tagCon integer (ℤ.negsuc 0)))) (UCon (tagCon integer (ℤ.pos 17))))) (UApp (UApp (UApp (UBuiltin expModInteger) (UCon (tagCon integer (ℤ.pos 18)))) (UCon (tagCon integer (ℤ.pos 1)))) (UCon (tagCon integer (ℤ.pos 17)))))) (UCon (tagCon integer (ℤ.pos 17))))) (UCon (tagCon integer (ℤ.pos 1))))

expected-expModInteger-47 : Result
expected-expModInteger-47 = success (UCon (tagCon bool true))

-- Pending: postulated builtin `expModInteger`.
pending-expModInteger-47 : Set
pending-expModInteger-47 = Pending (evalRaw test-expModInteger-47 ≡ expected-expModInteger-47)
```

## expModInteger-48

```
-- builtin/semantics/expModInteger/extra/expModInteger-48
-- m > 1, e = -1, gcd a m = 1 -> compute inverse
test-expModInteger-48 : Untyped
test-expModInteger-48 = (UApp (UApp (UBuiltin equalsInteger) (UApp (UApp (UBuiltin modInteger) (UApp (UApp (UBuiltin multiplyInteger) (UApp (UApp (UApp (UBuiltin expModInteger) (UCon (tagCon integer (ℤ.negsuc 1718)))) (UCon (tagCon integer (ℤ.negsuc 0)))) (UCon (tagCon integer (ℤ.pos 17))))) (UApp (UApp (UApp (UBuiltin expModInteger) (UCon (tagCon integer (ℤ.negsuc 1718)))) (UCon (tagCon integer (ℤ.pos 1)))) (UCon (tagCon integer (ℤ.pos 17)))))) (UCon (tagCon integer (ℤ.pos 17))))) (UCon (tagCon integer (ℤ.pos 1))))

expected-expModInteger-48 : Result
expected-expModInteger-48 = success (UCon (tagCon bool true))

-- Pending: postulated builtin `expModInteger`.
pending-expModInteger-48 : Set
pending-expModInteger-48 = Pending (evalRaw test-expModInteger-48 ≡ expected-expModInteger-48)
```

## expModInteger-49

```
-- builtin/semantics/expModInteger/extra/expModInteger-49
-- m = 3842610773*16548071329, e = -1 gcd a m = 1 -> compute inverse
test-expModInteger-49 : Untyped
test-expModInteger-49 = (UApp (UApp (UBuiltin equalsInteger) (UApp (UApp (UBuiltin modInteger) (UApp (UApp (UBuiltin multiplyInteger) (UApp (UApp (UApp (UBuiltin expModInteger) (UCon (tagCon integer (ℤ.pos 3842610771)))) (UCon (tagCon integer (ℤ.negsuc 0)))) (UCon (tagCon integer (ℤ.pos 63587797161187827317))))) (UApp (UApp (UApp (UBuiltin expModInteger) (UCon (tagCon integer (ℤ.pos 3842610771)))) (UCon (tagCon integer (ℤ.pos 1)))) (UCon (tagCon integer (ℤ.pos 63587797161187827317)))))) (UCon (tagCon integer (ℤ.pos 63587797161187827317))))) (UCon (tagCon integer (ℤ.pos 1))))

expected-expModInteger-49 : Result
expected-expModInteger-49 = success (UCon (tagCon bool true))

-- Pending: postulated builtin `expModInteger`.
pending-expModInteger-49 : Set
pending-expModInteger-49 = Pending (evalRaw test-expModInteger-49 ≡ expected-expModInteger-49)
```

## expModInteger-50

```
-- builtin/semantics/expModInteger/extra/expModInteger-50
-- m = 3842610773*16548071329, e = -1 gcd a m = 1 -> compute inverse
test-expModInteger-50 : Untyped
test-expModInteger-50 = (UApp (UApp (UBuiltin equalsInteger) (UApp (UApp (UBuiltin modInteger) (UApp (UApp (UBuiltin multiplyInteger) (UApp (UApp (UApp (UBuiltin expModInteger) (UCon (tagCon integer (ℤ.pos 1654807132907)))) (UCon (tagCon integer (ℤ.negsuc 0)))) (UCon (tagCon integer (ℤ.pos 63587797161187827317))))) (UApp (UApp (UApp (UBuiltin expModInteger) (UCon (tagCon integer (ℤ.pos 1654807132907)))) (UCon (tagCon integer (ℤ.pos 1)))) (UCon (tagCon integer (ℤ.pos 63587797161187827317)))))) (UCon (tagCon integer (ℤ.pos 63587797161187827317))))) (UCon (tagCon integer (ℤ.pos 1))))

expected-expModInteger-50 : Result
expected-expModInteger-50 = success (UCon (tagCon bool true))

-- Pending: postulated builtin `expModInteger`.
pending-expModInteger-50 : Set
pending-expModInteger-50 = Pending (evalRaw test-expModInteger-50 ≡ expected-expModInteger-50)
```

## expModInteger-51

```
-- builtin/semantics/expModInteger/extra/expModInteger-51
-- m > 1, e < 0, gcd a m = 1 -> compute inverse power
test-expModInteger-51 : Untyped
test-expModInteger-51 = (UApp (UApp (UBuiltin equalsInteger) (UApp (UApp (UBuiltin modInteger) (UApp (UApp (UBuiltin multiplyInteger) (UApp (UApp (UApp (UBuiltin expModInteger) (UCon (tagCon integer (ℤ.pos 1)))) (UCon (tagCon integer (ℤ.negsuc 1134134120)))) (UCon (tagCon integer (ℤ.pos 17))))) (UApp (UApp (UApp (UBuiltin expModInteger) (UCon (tagCon integer (ℤ.pos 1)))) (UCon (tagCon integer (ℤ.pos 1134134121)))) (UCon (tagCon integer (ℤ.pos 17)))))) (UCon (tagCon integer (ℤ.pos 17))))) (UCon (tagCon integer (ℤ.pos 1))))

expected-expModInteger-51 : Result
expected-expModInteger-51 = success (UCon (tagCon bool true))

-- Pending: postulated builtin `expModInteger`.
pending-expModInteger-51 : Set
pending-expModInteger-51 = Pending (evalRaw test-expModInteger-51 ≡ expected-expModInteger-51)
```

## expModInteger-52

```
-- builtin/semantics/expModInteger/extra/expModInteger-52
-- m > 1, e < 0, gcd a m = 1 -> compute inverse power
test-expModInteger-52 : Untyped
test-expModInteger-52 = (UApp (UApp (UBuiltin equalsInteger) (UApp (UApp (UBuiltin modInteger) (UApp (UApp (UBuiltin multiplyInteger) (UApp (UApp (UApp (UBuiltin expModInteger) (UCon (tagCon integer (ℤ.pos 18)))) (UCon (tagCon integer (ℤ.negsuc 4)))) (UCon (tagCon integer (ℤ.pos 17))))) (UApp (UApp (UApp (UBuiltin expModInteger) (UCon (tagCon integer (ℤ.pos 18)))) (UCon (tagCon integer (ℤ.pos 5)))) (UCon (tagCon integer (ℤ.pos 17)))))) (UCon (tagCon integer (ℤ.pos 17))))) (UCon (tagCon integer (ℤ.pos 1))))

expected-expModInteger-52 : Result
expected-expModInteger-52 = success (UCon (tagCon bool true))

-- Pending: postulated builtin `expModInteger`.
pending-expModInteger-52 : Set
pending-expModInteger-52 = Pending (evalRaw test-expModInteger-52 ≡ expected-expModInteger-52)
```

## expModInteger-53

```
-- builtin/semantics/expModInteger/extra/expModInteger-53
-- m > 1, e < 0, gcd a m = 1 -> compute inverse power
test-expModInteger-53 : Untyped
test-expModInteger-53 = (UApp (UApp (UBuiltin equalsInteger) (UApp (UApp (UBuiltin modInteger) (UApp (UApp (UBuiltin multiplyInteger) (UApp (UApp (UApp (UBuiltin expModInteger) (UCon (tagCon integer (ℤ.negsuc 1718)))) (UCon (tagCon integer (ℤ.negsuc 999999999999999999999999999999)))) (UCon (tagCon integer (ℤ.pos 17))))) (UApp (UApp (UApp (UBuiltin expModInteger) (UCon (tagCon integer (ℤ.negsuc 1718)))) (UCon (tagCon integer (ℤ.pos 1000000000000000000000000000000)))) (UCon (tagCon integer (ℤ.pos 17)))))) (UCon (tagCon integer (ℤ.pos 17))))) (UCon (tagCon integer (ℤ.pos 1))))

expected-expModInteger-53 : Result
expected-expModInteger-53 = success (UCon (tagCon bool true))

-- Pending: postulated builtin `expModInteger`.
pending-expModInteger-53 : Set
pending-expModInteger-53 = Pending (evalRaw test-expModInteger-53 ≡ expected-expModInteger-53)
```

## expModInteger-54

```
-- builtin/semantics/expModInteger/extra/expModInteger-54
-- m = 3842610773*16548071329, e < 0, gcd a m = 1 -> compute inverse power
test-expModInteger-54 : Untyped
test-expModInteger-54 = (UApp (UApp (UBuiltin equalsInteger) (UApp (UApp (UBuiltin modInteger) (UApp (UApp (UBuiltin multiplyInteger) (UApp (UApp (UApp (UBuiltin expModInteger) (UCon (tagCon integer (ℤ.pos 3842610771)))) (UCon (tagCon integer (ℤ.negsuc 777777777777777777777770)))) (UCon (tagCon integer (ℤ.pos 63587797161187827317))))) (UApp (UApp (UApp (UBuiltin expModInteger) (UCon (tagCon integer (ℤ.pos 3842610771)))) (UCon (tagCon integer (ℤ.pos 777777777777777777777771)))) (UCon (tagCon integer (ℤ.pos 63587797161187827317)))))) (UCon (tagCon integer (ℤ.pos 63587797161187827317))))) (UCon (tagCon integer (ℤ.pos 1))))

expected-expModInteger-54 : Result
expected-expModInteger-54 = success (UCon (tagCon bool true))

-- Pending: postulated builtin `expModInteger`.
pending-expModInteger-54 : Set
pending-expModInteger-54 = Pending (evalRaw test-expModInteger-54 ≡ expected-expModInteger-54)
```

## expModInteger-55

```
-- builtin/semantics/expModInteger/extra/expModInteger-55
-- m = 3842610773*16548071329, e < 0, gcd a m = 1 -> compute inverse power
test-expModInteger-55 : Untyped
test-expModInteger-55 = (UApp (UApp (UBuiltin equalsInteger) (UApp (UApp (UBuiltin modInteger) (UApp (UApp (UBuiltin multiplyInteger) (UApp (UApp (UApp (UBuiltin expModInteger) (UCon (tagCon integer (ℤ.pos 1654807132907)))) (UCon (tagCon integer (ℤ.negsuc 18446744073709551615)))) (UCon (tagCon integer (ℤ.pos 63587797161187827317))))) (UApp (UApp (UApp (UBuiltin expModInteger) (UCon (tagCon integer (ℤ.pos 1654807132907)))) (UCon (tagCon integer (ℤ.pos 18446744073709551616)))) (UCon (tagCon integer (ℤ.pos 63587797161187827317)))))) (UCon (tagCon integer (ℤ.pos 63587797161187827317))))) (UCon (tagCon integer (ℤ.pos 1))))

expected-expModInteger-55 : Result
expected-expModInteger-55 = success (UCon (tagCon bool true))

-- Pending: postulated builtin `expModInteger`.
pending-expModInteger-55 : Set
pending-expModInteger-55 = Pending (evalRaw test-expModInteger-55 ≡ expected-expModInteger-55)
```

## expModInteger-56

```
-- builtin/semantics/expModInteger/extra/expModInteger-56
-- Large inputs: m = 2^255-19
test-expModInteger-56 : Untyped
test-expModInteger-56 = (UApp (UApp (UApp (UBuiltin expModInteger) (UCon (tagCon integer (ℤ.pos 0)))) (UCon (tagCon integer (ℤ.pos 0)))) (UCon (tagCon integer (ℤ.pos 57896044618658097711785492504343953926634992332820282019728792003956564819949))))

expected-expModInteger-56 : Result
expected-expModInteger-56 = success (UCon (tagCon integer (ℤ.pos 1)))

-- Pending: postulated builtin `expModInteger`.
pending-expModInteger-56 : Set
pending-expModInteger-56 = Pending (evalRaw test-expModInteger-56 ≡ expected-expModInteger-56)
```

## expModInteger-57

```
-- builtin/semantics/expModInteger/extra/expModInteger-57
-- Large inputs: m = 2^255-19
test-expModInteger-57 : Untyped
test-expModInteger-57 = (UApp (UApp (UApp (UBuiltin expModInteger) (UCon (tagCon integer (ℤ.pos 2)))) (UCon (tagCon integer (ℤ.pos 64)))) (UCon (tagCon integer (ℤ.pos 57896044618658097711785492504343953926634992332820282019728792003956564819949))))

expected-expModInteger-57 : Result
expected-expModInteger-57 = success (UCon (tagCon integer (ℤ.pos 18446744073709551616)))

-- Pending: postulated builtin `expModInteger`.
pending-expModInteger-57 : Set
pending-expModInteger-57 = Pending (evalRaw test-expModInteger-57 ≡ expected-expModInteger-57)
```

## expModInteger-58

```
-- builtin/semantics/expModInteger/extra/expModInteger-58
-- Large inputs: m = 2^255-19
test-expModInteger-58 : Untyped
test-expModInteger-58 = (UApp (UApp (UApp (UBuiltin expModInteger) (UCon (tagCon integer (ℤ.pos 2)))) (UCon (tagCon integer (ℤ.negsuc 63)))) (UCon (tagCon integer (ℤ.pos 57896044618658097711785492504343953926634992332820282019728792003956564819949))))

expected-expModInteger-58 : Result
expected-expModInteger-58 = success (UCon (tagCon integer (ℤ.pos 30471602430872683006368077679533309455171990423147718600281005145357771866102)))

-- Pending: postulated builtin `expModInteger`.
pending-expModInteger-58 : Set
pending-expModInteger-58 = Pending (evalRaw test-expModInteger-58 ≡ expected-expModInteger-58)
```

## expModInteger-59

```
-- builtin/semantics/expModInteger/extra/expModInteger-59
-- Large inputs: m = 2^255-19
test-expModInteger-59 : Untyped
test-expModInteger-59 = (UApp (UApp (UApp (UBuiltin expModInteger) (UCon (tagCon integer (ℤ.pos 295783465278346578267348527836475862348589358937497)))) (UCon (tagCon integer (ℤ.pos 89734578923487957289347527893478952378945268423487234782378423)))) (UCon (tagCon integer (ℤ.pos 57896044618658097711785492504343953926634992332820282019728792003956564819949))))

expected-expModInteger-59 : Result
expected-expModInteger-59 = success (UCon (tagCon integer (ℤ.pos 32206691988103784342539609430659656895837532833998353585585601025665197189770)))

-- Pending: postulated builtin `expModInteger`.
pending-expModInteger-59 : Set
pending-expModInteger-59 = Pending (evalRaw test-expModInteger-59 ≡ expected-expModInteger-59)
```

## expModInteger-60

```
-- builtin/semantics/expModInteger/extra/expModInteger-60
-- Large inputs: m = 2^255-19
test-expModInteger-60 : Untyped
test-expModInteger-60 = (UApp (UApp (UApp (UBuiltin expModInteger) (UCon (tagCon integer (ℤ.negsuc 278903489723894263784627895384582367892349236727345)))) (UCon (tagCon integer (ℤ.pos 2782346783647862783469234789237848236498238946918723789178293)))) (UCon (tagCon integer (ℤ.pos 57896044618658097711785492504343953926634992332820282019728792003956564819949))))

expected-expModInteger-60 : Result
expected-expModInteger-60 = success (UCon (tagCon integer (ℤ.pos 41639481880816845111909653885891797604671528343369469127307248315308458868975)))

-- Pending: postulated builtin `expModInteger`.
pending-expModInteger-60 : Set
pending-expModInteger-60 = Pending (evalRaw test-expModInteger-60 ≡ expected-expModInteger-60)
```

## expModInteger-61

```
-- builtin/semantics/expModInteger/extra/expModInteger-61
-- Large inputs: m = 2^255-19
test-expModInteger-61 : Untyped
test-expModInteger-61 = (UApp (UApp (UApp (UBuiltin expModInteger) (UCon (tagCon integer (ℤ.pos 11111111111111111111111111111111111111111111111111111111111111111789427389478923)))) (UCon (tagCon integer (ℤ.negsuc 789239427389489234897829734789283974892734897283974897238947234722233)))) (UCon (tagCon integer (ℤ.pos 57896044618658097711785492504343953926634992332820282019728792003956564819949))))

expected-expModInteger-61 : Result
expected-expModInteger-61 = success (UCon (tagCon integer (ℤ.pos 9490012894827172785774821291029803814876173214515365770785362878234508261242)))

-- Pending: postulated builtin `expModInteger`.
pending-expModInteger-61 : Set
pending-expModInteger-61 = Pending (evalRaw test-expModInteger-61 ≡ expected-expModInteger-61)
```

## expModInteger-62

```
-- builtin/semantics/expModInteger/extra/expModInteger-62
-- Large inputs: m = 2^255-19
test-expModInteger-62 : Untyped
test-expModInteger-62 = (UApp (UApp (UApp (UBuiltin expModInteger) (UCon (tagCon integer (ℤ.negsuc 11111111111111111111111111111111111111111111111111111111111111111789427389478922)))) (UCon (tagCon integer (ℤ.negsuc 789239427389489234897829734789283974892734897283974897238947234722233)))) (UCon (tagCon integer (ℤ.pos 57896044618658097711785492504343953926634992332820282019728792003956564819949))))

expected-expModInteger-62 : Result
expected-expModInteger-62 = success (UCon (tagCon integer (ℤ.pos 9490012894827172785774821291029803814876173214515365770785362878234508261242)))

-- Pending: postulated builtin `expModInteger`.
pending-expModInteger-62 : Set
pending-expModInteger-62 = Pending (evalRaw test-expModInteger-62 ≡ expected-expModInteger-62)
```

## expModInteger-63

```
-- builtin/semantics/expModInteger/extra/expModInteger-63
-- Large inputs: m = 2^255-19, e = m-1
test-expModInteger-63 : Untyped
test-expModInteger-63 = (UApp (UApp (UApp (UBuiltin expModInteger) (UCon (tagCon integer (ℤ.pos 289342903489028349034589023745823457892346934785623452334786341567142314)))) (UCon (tagCon integer (ℤ.pos 57896044618658097711785492504343953926634992332820282019728792003956564819948)))) (UCon (tagCon integer (ℤ.pos 57896044618658097711785492504343953926634992332820282019728792003956564819949))))

expected-expModInteger-63 : Result
expected-expModInteger-63 = success (UCon (tagCon integer (ℤ.pos 1)))

-- Pending: postulated builtin `expModInteger`.
pending-expModInteger-63 : Set
pending-expModInteger-63 = Pending (evalRaw test-expModInteger-63 ≡ expected-expModInteger-63)
```

## expModInteger-64

```
-- builtin/semantics/expModInteger/extra/expModInteger-64
-- Large inputs: m = 2^255-19, e = -(m-1)
test-expModInteger-64 : Untyped
test-expModInteger-64 = (UApp (UApp (UApp (UBuiltin expModInteger) (UCon (tagCon integer (ℤ.pos 99999999999999999999999999999999999999999999999999999999999999999999999999999999999)))) (UCon (tagCon integer (ℤ.negsuc 57896044618658097711785492504343953926634992332820282019728792003956564819947)))) (UCon (tagCon integer (ℤ.pos 57896044618658097711785492504343953926634992332820282019728792003956564819949))))

expected-expModInteger-64 : Result
expected-expModInteger-64 = success (UCon (tagCon integer (ℤ.pos 1)))

-- Pending: postulated builtin `expModInteger`.
pending-expModInteger-64 : Set
pending-expModInteger-64 = Pending (evalRaw test-expModInteger-64 ≡ expected-expModInteger-64)
```

## expModInteger-65

```
-- builtin/semantics/expModInteger/extra/expModInteger-65
-- Large inputs: m = 2^255-19, e = 10000*(m-1)
test-expModInteger-65 : Untyped
test-expModInteger-65 = (UApp (UApp (UApp (UBuiltin expModInteger) (UCon (tagCon integer (ℤ.pos 289342903489028349034589023745823457892346934785623452334786341567142314)))) (UCon (tagCon integer (ℤ.pos 578960446186580977117854925043439539266349923328202820197287920039565648199480000)))) (UCon (tagCon integer (ℤ.pos 57896044618658097711785492504343953926634992332820282019728792003956564819949))))

expected-expModInteger-65 : Result
expected-expModInteger-65 = success (UCon (tagCon integer (ℤ.pos 1)))

-- Pending: postulated builtin `expModInteger`.
pending-expModInteger-65 : Set
pending-expModInteger-65 = Pending (evalRaw test-expModInteger-65 ≡ expected-expModInteger-65)
```

## expModInteger-66

```
-- builtin/semantics/expModInteger/extra/expModInteger-66
-- Large inputs: m = 2^255-19, e = -10000*(m-1)
test-expModInteger-66 : Untyped
test-expModInteger-66 = (UApp (UApp (UApp (UBuiltin expModInteger) (UCon (tagCon integer (ℤ.pos 99999999999999999999999999999999999999999999999999999999999999999999999999999999999)))) (UCon (tagCon integer (ℤ.negsuc 578960446186580977117854925043439539266349923328202820197287920039565648199479999)))) (UCon (tagCon integer (ℤ.pos 57896044618658097711785492504343953926634992332820282019728792003956564819949))))

expected-expModInteger-66 : Result
expected-expModInteger-66 = success (UCon (tagCon integer (ℤ.pos 1)))

-- Pending: postulated builtin `expModInteger`.
pending-expModInteger-66 : Set
pending-expModInteger-66 = Pending (evalRaw test-expModInteger-66 ≡ expected-expModInteger-66)
```

## expModInteger-67

```
-- builtin/semantics/expModInteger/extra/expModInteger-67
-- Large inputs: m = 79!
test-expModInteger-67 : Untyped
test-expModInteger-67 = (UApp (UApp (UApp (UBuiltin expModInteger) (UCon (tagCon integer (ℤ.pos 0)))) (UCon (tagCon integer (ℤ.pos 0)))) (UCon (tagCon integer (ℤ.pos 894618213078297528685144171539831652069808216779571907213868063227837990693501860533361810841010176000000000000000000))))

expected-expModInteger-67 : Result
expected-expModInteger-67 = success (UCon (tagCon integer (ℤ.pos 1)))

-- Pending: postulated builtin `expModInteger`.
pending-expModInteger-67 : Set
pending-expModInteger-67 = Pending (evalRaw test-expModInteger-67 ≡ expected-expModInteger-67)
```

## expModInteger-68

```
-- builtin/semantics/expModInteger/extra/expModInteger-68
-- Large inputs: m = 79!
test-expModInteger-68 : Untyped
test-expModInteger-68 = (UApp (UApp (UApp (UBuiltin expModInteger) (UCon (tagCon integer (ℤ.pos 2)))) (UCon (tagCon integer (ℤ.pos 64)))) (UCon (tagCon integer (ℤ.pos 894618213078297528685144171539831652069808216779571907213868063227837990693501860533361810841010176000000000000000000))))

expected-expModInteger-68 : Result
expected-expModInteger-68 = success (UCon (tagCon integer (ℤ.pos 18446744073709551616)))

-- Pending: postulated builtin `expModInteger`.
pending-expModInteger-68 : Set
pending-expModInteger-68 = Pending (evalRaw test-expModInteger-68 ≡ expected-expModInteger-68)
```

## expModInteger-69

```
-- builtin/semantics/expModInteger/extra/expModInteger-69
-- Large inputs: m = 79! -> fail (gcd > 1)
test-expModInteger-69 : Untyped
test-expModInteger-69 = (UApp (UApp (UApp (UBuiltin expModInteger) (UCon (tagCon integer (ℤ.pos 2)))) (UCon (tagCon integer (ℤ.negsuc 63)))) (UCon (tagCon integer (ℤ.pos 894618213078297528685144171539831652069808216779571907213868063227837990693501860533361810841010176000000000000000000))))

expected-expModInteger-69 : Result
expected-expModInteger-69 = failure

-- Pending: postulated builtin `expModInteger`.
pending-expModInteger-69 : Set
pending-expModInteger-69 = Pending (evalRaw test-expModInteger-69 ≡ expected-expModInteger-69)
```

## expModInteger-70

```
-- builtin/semantics/expModInteger/extra/expModInteger-70
-- Large inputs: m = 79!
test-expModInteger-70 : Untyped
test-expModInteger-70 = (UApp (UApp (UApp (UBuiltin expModInteger) (UCon (tagCon integer (ℤ.pos 295783465278346578267348527836475862348589358937497)))) (UCon (tagCon integer (ℤ.pos 89734578923487957289347527893478952378945268423487234782378423)))) (UCon (tagCon integer (ℤ.pos 894618213078297528685144171539831652069808216779571907213868063227837990693501860533361810841010176000000000000000000))))

expected-expModInteger-70 : Result
expected-expModInteger-70 = success (UCon (tagCon integer (ℤ.pos 280175799933420074585178470510090012806707950340412289432212739835789837904455835552327022379259130346551828535037673)))

-- Pending: postulated builtin `expModInteger`.
pending-expModInteger-70 : Set
pending-expModInteger-70 = Pending (evalRaw test-expModInteger-70 ≡ expected-expModInteger-70)
```

## expModInteger-71

```
-- builtin/semantics/expModInteger/extra/expModInteger-71
-- Large inputs: m = 79!
test-expModInteger-71 : Untyped
test-expModInteger-71 = (UApp (UApp (UApp (UBuiltin expModInteger) (UCon (tagCon integer (ℤ.negsuc 278903489723894263784627895384582367892349236727345)))) (UCon (tagCon integer (ℤ.pos 2782346783647862783469234789237848236498238946918723789178293)))) (UCon (tagCon integer (ℤ.pos 894618213078297528685144171539831652069808216779571907213868063227837990693501860533361810841010176000000000000000000))))

expected-expModInteger-71 : Result
expected-expModInteger-71 = success (UCon (tagCon integer (ℤ.pos 676608236808522252873008336960453539807071928324507727553824692454236867626155713650291062437090100975669387894718464)))

-- Pending: postulated builtin `expModInteger`.
pending-expModInteger-71 : Set
pending-expModInteger-71 = Pending (evalRaw test-expModInteger-71 ≡ expected-expModInteger-71)
```

## expModInteger-72

```
-- builtin/semantics/expModInteger/extra/expModInteger-72
-- Large inputs: m = 79!
test-expModInteger-72 : Untyped
test-expModInteger-72 = (UApp (UApp (UApp (UBuiltin expModInteger) (UCon (tagCon integer (ℤ.pos 11111111111111111111111111111111111111111111111111111111111111111789427389478923)))) (UCon (tagCon integer (ℤ.negsuc 789239427389489234897829734789283974892734897283974897238947234722233)))) (UCon (tagCon integer (ℤ.pos 894618213078297528685144171539831652069808216779571907213868063227837990693501860533361810841010176000000000000000000))))

expected-expModInteger-72 : Result
expected-expModInteger-72 = success (UCon (tagCon integer (ℤ.pos 226253110172970512032322077499046610917698223745805046643293407253856550947890147970889384902312109044059858650440489)))

-- Pending: postulated builtin `expModInteger`.
pending-expModInteger-72 : Set
pending-expModInteger-72 = Pending (evalRaw test-expModInteger-72 ≡ expected-expModInteger-72)
```

## expModInteger-73

```
-- builtin/semantics/expModInteger/extra/expModInteger-73
-- Large inputs: m = 79!
test-expModInteger-73 : Untyped
test-expModInteger-73 = (UApp (UApp (UApp (UBuiltin expModInteger) (UCon (tagCon integer (ℤ.negsuc 11111111111111111111111111111111111111111111111111111111111111111789427389478922)))) (UCon (tagCon integer (ℤ.negsuc 789239427389489234897829734789283974892734897283974897238947234722233)))) (UCon (tagCon integer (ℤ.pos 894618213078297528685144171539831652069808216779571907213868063227837990693501860533361810841010176000000000000000000))))

expected-expModInteger-73 : Result
expected-expModInteger-73 = success (UCon (tagCon integer (ℤ.pos 226253110172970512032322077499046610917698223745805046643293407253856550947890147970889384902312109044059858650440489)))

-- Pending: postulated builtin `expModInteger`.
pending-expModInteger-73 : Set
pending-expModInteger-73 = Pending (evalRaw test-expModInteger-73 ≡ expected-expModInteger-73)
```

## expModInteger-74

```
-- builtin/semantics/expModInteger/extra/expModInteger-74
-- Large inputs: m = 79!, e = m-1
test-expModInteger-74 : Untyped
test-expModInteger-74 = (UApp (UApp (UApp (UBuiltin expModInteger) (UCon (tagCon integer (ℤ.pos 289342903489028349034589023745823457892346934785623452334786341567142314)))) (UCon (tagCon integer (ℤ.pos 894618213078297528685144171539831652069808216779571907213868063227837990693501860533361810841010175999999999999999999)))) (UCon (tagCon integer (ℤ.pos 894618213078297528685144171539831652069808216779571907213868063227837990693501860533361810841010176000000000000000000))))

expected-expModInteger-74 : Result
expected-expModInteger-74 = success (UCon (tagCon integer (ℤ.pos 799213302676025590986559862430737311371208606877556070099461944686298161515921765132026310527039911779485954640707584)))

-- Pending: postulated builtin `expModInteger`.
pending-expModInteger-74 : Set
pending-expModInteger-74 = Pending (evalRaw test-expModInteger-74 ≡ expected-expModInteger-74)
```

## expModInteger-75

```
-- builtin/semantics/expModInteger/extra/expModInteger-75
-- Large inputs: m = 79!, e = -(m-1), a = 2^255-19
test-expModInteger-75 : Untyped
test-expModInteger-75 = (UApp (UApp (UApp (UBuiltin expModInteger) (UCon (tagCon integer (ℤ.pos 57896044618658097711785492504343953926634992332820282019728792003956564819949)))) (UCon (tagCon integer (ℤ.negsuc 894618213078297528685144171539831652069808216779571907213868063227837990693501860533361810841010175999999999999999998)))) (UCon (tagCon integer (ℤ.pos 894618213078297528685144171539831652069808216779571907213868063227837990693501860533361810841010176000000000000000000))))

expected-expModInteger-75 : Result
expected-expModInteger-75 = success (UCon (tagCon integer (ℤ.pos 57896044618658097711785492504343953926634992332820282019728792003956564819949)))

-- Pending: postulated builtin `expModInteger`.
pending-expModInteger-75 : Set
pending-expModInteger-75 = Pending (evalRaw test-expModInteger-75 ≡ expected-expModInteger-75)
```

## expModInteger-76

```
-- builtin/semantics/expModInteger/extra/expModInteger-76
-- Large inputs: m = 79!, e = 10000*(m-1)
test-expModInteger-76 : Untyped
test-expModInteger-76 = (UApp (UApp (UApp (UBuiltin expModInteger) (UCon (tagCon integer (ℤ.pos 289342903489028349034589023745823457892346934785623452334786341567142314)))) (UCon (tagCon integer (ℤ.pos 8946182130782975286851441715398316520698082167795719072138680632278379906935018605333618108410101759999999999999999990000)))) (UCon (tagCon integer (ℤ.pos 894618213078297528685144171539831652069808216779571907213868063227837990693501860533361810841010176000000000000000000))))

expected-expModInteger-76 : Result
expected-expModInteger-76 = success (UCon (tagCon integer (ℤ.pos 126589639180843360572550169437466175160404232405174811173487450267795410776435354182712112924966658652508478689509376)))

-- Pending: postulated builtin `expModInteger`.
pending-expModInteger-76 : Set
pending-expModInteger-76 = Pending (evalRaw test-expModInteger-76 ≡ expected-expModInteger-76)
```

## expModInteger-77

```
-- builtin/semantics/expModInteger/extra/expModInteger-77
-- Large inputs: m = 79!, e = -10000*(m-1), a = 2^255-19
test-expModInteger-77 : Untyped
test-expModInteger-77 = (UApp (UApp (UApp (UBuiltin expModInteger) (UCon (tagCon integer (ℤ.pos 57896044618658097711785492504343953926634992332820282019728792003956564819949)))) (UCon (tagCon integer (ℤ.negsuc 8946182130782975286851441715398316520698082167795719072138680632278379906935018605333618108410101759999999999999999989999)))) (UCon (tagCon integer (ℤ.pos 894618213078297528685144171539831652069808216779571907213868063227837990693501860533361810841010176000000000000000000))))

expected-expModInteger-77 : Result
expected-expModInteger-77 = success (UCon (tagCon integer (ℤ.pos 267938415452876215619736915735930925390188109664796165617656900154039538886782993138509072889964389462027704913000001)))

-- Pending: postulated builtin `expModInteger`.
pending-expModInteger-77 : Set
pending-expModInteger-77 = Pending (evalRaw test-expModInteger-77 ≡ expected-expModInteger-77)
```
