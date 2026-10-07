---
title: Conformance.Builtin.Semantics.Bls12381G2ScalarMul
layout: page
---

<!-- GENERATED FILE: do not edit.
     Regenerate with `cabal run plutus-conformance:generate-agda-conformance`
     from the repository root. -->

Conformance tests generated from
`plutus-conformance/test-cases/uplc/evaluation/builtin/semantics/bls12_381_G2_scalarMul`.
See `Conformance.Eval` for how they are run.

```
module Conformance.Builtin.Semantics.Bls12381G2ScalarMul where

open import Conformance.Eval
```

## addmul

```
-- builtin/semantics/bls12_381_G2_scalarMul/addmul
-- 2157p + 2157q for random points p and q in G2.  This should give the same result as muladd.
test-addmul : Untyped
test-addmul = (UApp (UBuiltin bls12-381-G2-compress) (UApp (UApp (UBuiltin bls12-381-G2-add) (UApp (UApp (UBuiltin bls12-381-G2-scalarMul) (UCon (tagCon integer (ℤ.pos 2157)))) (UApp (UBuiltin bls12-381-G2-uncompress) (UCon (tagCon bytestring (mkByteString "\176b\159\161\NAK\140-#\161\EOT\DC3\254\145\211\129\168M%\227\GS\EOT\FS\208\&7}%\130\132\152\253\STX\SOH\ESC5\137\&98\206\217u59^H\NAK \RSg\DLE\139\205Fe\224\219%\214\STX\215o\167\145\250\183\ACK\197J\191^\SUB\158D\180\172\RSk\173\243\210\172\ETX(\245\227\v\227Ag|\139\172]\218v\130\241")))))) (UApp (UApp (UBuiltin bls12-381-G2-scalarMul) (UCon (tagCon integer (ℤ.pos 2157)))) (UApp (UBuiltin bls12-381-G2-uncompress) (UCon (tagCon bytestring (mkByteString "\131\DLE\188\151\252z\217\177anQ\"ljR\ESC\157\DEL\223\ETX\247)\152\&3\230\162\b\174\ETX\153\254\199`E\164<\238\248F\224\149\141\f\223\ENQ\207+\US\NULF\SO\230\237\210w\139A>\183\194r\188[\148\209+\145\SI\138\196\235\ESCU\229\n\147dG\DC4xt\ETB\188F#I\197\224\246\243W\185\172\&2&*")))))))

expected-addmul : Result
expected-addmul = success (UCon (tagCon bytestring (mkByteString "\184\163\&5\205\187=\231D\186+k\179\201\173\156 \154\DEL3\161E<.\208F\SO\CAN\140\US1\241\133\227Y\166''\254\GS\139\165\201\&1\215^\246D\229\SOHs\229%[b\EMFw\251g2<\228+\172\\k\ESC\a~h-\243\170\188\161\202\238/d\r\177\254\208\180\173Q\NAKb\247\197M\132\234v\222\188")))

-- Pending: bytestring constant; postulated builtin `bls12-381-G2-compress`; postulated builtin `bls12-381-G2-add`; postulated builtin `bls12-381-G2-scalarMul`; postulated builtin `bls12-381-G2-uncompress`.
pending-addmul : Set
pending-addmul = Pending (evalRaw test-addmul ≡ expected-addmul)
```

## mul-44

```
-- builtin/semantics/bls12_381_G2_scalarMul/mul-44
-- Check that multiplication by the scalar 44 gives the expected result.
test-mul-44 : Untyped
test-mul-44 = (UApp (UBuiltin bls12-381-G2-compress) (UApp (UApp (UBuiltin bls12-381-G2-scalarMul) (UCon (tagCon integer (ℤ.pos 44)))) (UApp (UBuiltin bls12-381-G2-uncompress) (UCon (tagCon bytestring (mkByteString "\131\DLE\188\151\252z\217\177anQ\"ljR\ESC\157\DEL\223\ETX\247)\152\&3\230\162\b\174\ETX\153\254\199`E\164<\238\248F\224\149\141\f\223\ENQ\207+\US\NULF\SO\230\237\210w\139A>\183\194r\188[\148\209+\145\SI\138\196\235\ESCU\229\n\147dG\DC4xt\ETB\188F#I\197\224\246\243W\185\172\&2&*"))))))

expected-mul-44 : Result
expected-mul-44 = success (UCon (tagCon bytestring (mkByteString "\170*\149\188\153\&6\198\USP9\204o\187\224\226_\168\177R\142\161\140[\224\156\147\237\148\GS\FS\144RYp\134\184\211\179\181\251\189\DC1\f\227\137\&7\140T\DC4\239\211\DLE\222! \167\239\186\175p\208\US[\128\131Q\CAN\193\243\154Bs\161\SI\US*J\240\237\&3\167\193\DEL\186L\142?|\176\138\GS\151\232-V\DC1")))

-- Pending: bytestring constant; postulated builtin `bls12-381-G2-compress`; postulated builtin `bls12-381-G2-scalarMul`; postulated builtin `bls12-381-G2-uncompress`.
pending-mul-44 : Set
pending-mul-44 = Pending (evalRaw test-mul-44 ≡ expected-mul-44)
```

## mul-neg-one

```
-- builtin/semantics/bls12_381_G2_scalarMul/mul-neg-one
-- Check that the result of multiplying by -1 is as expected.
test-mul-neg-one : Untyped
test-mul-neg-one = (UApp (UBuiltin bls12-381-G2-compress) (UApp (UApp (UBuiltin bls12-381-G2-scalarMul) (UCon (tagCon integer (ℤ.negsuc 0)))) (UApp (UBuiltin bls12-381-G2-uncompress) (UCon (tagCon bytestring (mkByteString "\131\DLE\188\151\252z\217\177anQ\"ljR\ESC\157\DEL\223\ETX\247)\152\&3\230\162\b\174\ETX\153\254\199`E\164<\238\248F\224\149\141\f\223\ENQ\207+\US\NULF\SO\230\237\210w\139A>\183\194r\188[\148\209+\145\SI\138\196\235\ESCU\229\n\147dG\DC4xt\ETB\188F#I\197\224\246\243W\185\172\&2&*"))))))

expected-mul-neg-one : Result
expected-mul-neg-one = success (UCon (tagCon bytestring (mkByteString "\163\DLE\188\151\252z\217\177anQ\"ljR\ESC\157\DEL\223\ETX\247)\152\&3\230\162\b\174\ETX\153\254\199`E\164<\238\248F\224\149\141\f\223\ENQ\207+\US\NULF\SO\230\237\210w\139A>\183\194r\188[\148\209+\145\SI\138\196\235\ESCU\229\n\147dG\DC4xt\ETB\188F#I\197\224\246\243W\185\172\&2&*")))

-- Pending: bytestring constant; postulated builtin `bls12-381-G2-compress`; postulated builtin `bls12-381-G2-scalarMul`; postulated builtin `bls12-381-G2-uncompress`.
pending-mul-neg-one : Set
pending-mul-neg-one = Pending (evalRaw test-mul-neg-one ≡ expected-mul-neg-one)
```

## mul-one

```
-- builtin/semantics/bls12_381_G2_scalarMul/mul-one
-- Scalar multiplication by 1 leaves a random point unchanged.
test-mul-one : Untyped
test-mul-one = (UApp (UBuiltin bls12-381-G2-compress) (UApp (UApp (UBuiltin bls12-381-G2-scalarMul) (UCon (tagCon integer (ℤ.pos 1)))) (UApp (UBuiltin bls12-381-G2-uncompress) (UCon (tagCon bytestring (mkByteString "\131\DLE\188\151\252z\217\177anQ\"ljR\ESC\157\DEL\223\ETX\247)\152\&3\230\162\b\174\ETX\153\254\199`E\164<\238\248F\224\149\141\f\223\ENQ\207+\US\NULF\SO\230\237\210w\139A>\183\194r\188[\148\209+\145\SI\138\196\235\ESCU\229\n\147dG\DC4xt\ETB\188F#I\197\224\246\243W\185\172\&2&*"))))))

expected-mul-one : Result
expected-mul-one = success (UCon (tagCon bytestring (mkByteString "\131\DLE\188\151\252z\217\177anQ\"ljR\ESC\157\DEL\223\ETX\247)\152\&3\230\162\b\174\ETX\153\254\199`E\164<\238\248F\224\149\141\f\223\ENQ\207+\US\NULF\SO\230\237\210w\139A>\183\194r\188[\148\209+\145\SI\138\196\235\ESCU\229\n\147dG\DC4xt\ETB\188F#I\197\224\246\243W\185\172\&2&*")))

-- Pending: bytestring constant; postulated builtin `bls12-381-G2-compress`; postulated builtin `bls12-381-G2-scalarMul`; postulated builtin `bls12-381-G2-uncompress`.
pending-mul-one : Set
pending-mul-one = Pending (evalRaw test-mul-one ≡ expected-mul-one)
```

## mul-zero

```
-- builtin/semantics/bls12_381_G2_scalarMul/mul-zero
-- Multiplication by the zero scalar gives the zero point of G2.
test-mul-zero : Untyped
test-mul-zero = (UApp (UBuiltin bls12-381-G2-compress) (UApp (UApp (UBuiltin bls12-381-G2-scalarMul) (UCon (tagCon integer (ℤ.pos 0)))) (UApp (UBuiltin bls12-381-G2-uncompress) (UCon (tagCon bytestring (mkByteString "\131\DLE\188\151\252z\217\177anQ\"ljR\ESC\157\DEL\223\ETX\247)\152\&3\230\162\b\174\ETX\153\254\199`E\164<\238\248F\224\149\141\f\223\ENQ\207+\US\NULF\SO\230\237\210w\139A>\183\194r\188[\148\209+\145\SI\138\196\235\ESCU\229\n\147dG\DC4xt\ETB\188F#I\197\224\246\243W\185\172\&2&*"))))))

expected-mul-zero : Result
expected-mul-zero = success (UCon (tagCon bytestring (mkByteString "\192\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL")))

-- Pending: bytestring constant; postulated builtin `bls12-381-G2-compress`; postulated builtin `bls12-381-G2-scalarMul`; postulated builtin `bls12-381-G2-uncompress`.
pending-mul-zero : Set
pending-mul-zero = Pending (evalRaw test-mul-zero ≡ expected-mul-zero)
```

## mul19+25

```
-- builtin/semantics/bls12_381_G2_scalarMul/mul19+25
-- 19p+25p for a random point p in G2.  This should give the same result as mul44.
test-mul19-25 : Untyped
test-mul19-25 = (UApp (UBuiltin bls12-381-G2-compress) (UApp (UApp (UBuiltin bls12-381-G2-add) (UApp (UApp (UBuiltin bls12-381-G2-scalarMul) (UCon (tagCon integer (ℤ.pos 19)))) (UApp (UBuiltin bls12-381-G2-uncompress) (UCon (tagCon bytestring (mkByteString "\131\DLE\188\151\252z\217\177anQ\"ljR\ESC\157\DEL\223\ETX\247)\152\&3\230\162\b\174\ETX\153\254\199`E\164<\238\248F\224\149\141\f\223\ENQ\207+\US\NULF\SO\230\237\210w\139A>\183\194r\188[\148\209+\145\SI\138\196\235\ESCU\229\n\147dG\DC4xt\ETB\188F#I\197\224\246\243W\185\172\&2&*")))))) (UApp (UApp (UBuiltin bls12-381-G2-scalarMul) (UCon (tagCon integer (ℤ.pos 25)))) (UApp (UBuiltin bls12-381-G2-uncompress) (UCon (tagCon bytestring (mkByteString "\131\DLE\188\151\252z\217\177anQ\"ljR\ESC\157\DEL\223\ETX\247)\152\&3\230\162\b\174\ETX\153\254\199`E\164<\238\248F\224\149\141\f\223\ENQ\207+\US\NULF\SO\230\237\210w\139A>\183\194r\188[\148\209+\145\SI\138\196\235\ESCU\229\n\147dG\DC4xt\ETB\188F#I\197\224\246\243W\185\172\&2&*")))))))

expected-mul19-25 : Result
expected-mul19-25 = success (UCon (tagCon bytestring (mkByteString "\170*\149\188\153\&6\198\USP9\204o\187\224\226_\168\177R\142\161\140[\224\156\147\237\148\GS\FS\144RYp\134\184\211\179\181\251\189\DC1\f\227\137\&7\140T\DC4\239\211\DLE\222! \167\239\186\175p\208\US[\128\131Q\CAN\193\243\154Bs\161\SI\US*J\240\237\&3\167\193\DEL\186L\142?|\176\138\GS\151\232-V\DC1")))

-- Pending: bytestring constant; postulated builtin `bls12-381-G2-compress`; postulated builtin `bls12-381-G2-add`; postulated builtin `bls12-381-G2-scalarMul`; postulated builtin `bls12-381-G2-uncompress`.
pending-mul19-25 : Set
pending-mul19-25 = Pending (evalRaw test-mul19-25 ≡ expected-mul19-25)
```

## mul4x-11

```
-- builtin/semantics/bls12_381_G2_scalarMul/mul4x-11
-- 4*(11*p) for a point in G2.  This should give the same result as mul44.
test-mul4x-11 : Untyped
test-mul4x-11 = (UApp (UBuiltin bls12-381-G2-compress) (UApp (UApp (UBuiltin bls12-381-G2-scalarMul) (UCon (tagCon integer (ℤ.pos 4)))) (UApp (UApp (UBuiltin bls12-381-G2-scalarMul) (UCon (tagCon integer (ℤ.pos 11)))) (UApp (UBuiltin bls12-381-G2-uncompress) (UCon (tagCon bytestring (mkByteString "\131\DLE\188\151\252z\217\177anQ\"ljR\ESC\157\DEL\223\ETX\247)\152\&3\230\162\b\174\ETX\153\254\199`E\164<\238\248F\224\149\141\f\223\ENQ\207+\US\NULF\SO\230\237\210w\139A>\183\194r\188[\148\209+\145\SI\138\196\235\ESCU\229\n\147dG\DC4xt\ETB\188F#I\197\224\246\243W\185\172\&2&*")))))))

expected-mul4x-11 : Result
expected-mul4x-11 = success (UCon (tagCon bytestring (mkByteString "\170*\149\188\153\&6\198\USP9\204o\187\224\226_\168\177R\142\161\140[\224\156\147\237\148\GS\FS\144RYp\134\184\211\179\181\251\189\DC1\f\227\137\&7\140T\DC4\239\211\DLE\222! \167\239\186\175p\208\US[\128\131Q\CAN\193\243\154Bs\161\SI\US*J\240\237\&3\167\193\DEL\186L\142?|\176\138\GS\151\232-V\DC1")))

-- Pending: bytestring constant; postulated builtin `bls12-381-G2-compress`; postulated builtin `bls12-381-G2-scalarMul`; postulated builtin `bls12-381-G2-uncompress`.
pending-mul4x-11 : Set
pending-mul4x-11 = Pending (evalRaw test-mul4x-11 ≡ expected-mul4x-11)
```

## muladd

```
-- builtin/semantics/bls12_381_G2_scalarMul/muladd
-- n(p+q) = np + nq (n scalar, p and q random points in G2).
test-muladd : Untyped
test-muladd = (UApp (UBuiltin bls12-381-G2-compress) (UApp (UApp (UBuiltin bls12-381-G2-scalarMul) (UCon (tagCon integer (ℤ.pos 2157)))) (UApp (UApp (UBuiltin bls12-381-G2-add) (UApp (UBuiltin bls12-381-G2-uncompress) (UCon (tagCon bytestring (mkByteString "\176b\159\161\NAK\140-#\161\EOT\DC3\254\145\211\129\168M%\227\GS\EOT\FS\208\&7}%\130\132\152\253\STX\SOH\ESC5\137\&98\206\217u59^H\NAK \RSg\DLE\139\205Fe\224\219%\214\STX\215o\167\145\250\183\ACK\197J\191^\SUB\158D\180\172\RSk\173\243\210\172\ETX(\245\227\v\227Ag|\139\172]\218v\130\241"))))) (UApp (UBuiltin bls12-381-G2-uncompress) (UCon (tagCon bytestring (mkByteString "\131\DLE\188\151\252z\217\177anQ\"ljR\ESC\157\DEL\223\ETX\247)\152\&3\230\162\b\174\ETX\153\254\199`E\164<\238\248F\224\149\141\f\223\ENQ\207+\US\NULF\SO\230\237\210w\139A>\183\194r\188[\148\209+\145\SI\138\196\235\ESCU\229\n\147dG\DC4xt\ETB\188F#I\197\224\246\243W\185\172\&2&*")))))))

expected-muladd : Result
expected-muladd = success (UCon (tagCon bytestring (mkByteString "\184\163\&5\205\187=\231D\186+k\179\201\173\156 \154\DEL3\161E<.\208F\SO\CAN\140\US1\241\133\227Y\166''\254\GS\139\165\201\&1\215^\246D\229\SOHs\229%[b\EMFw\251g2<\228+\172\\k\ESC\a~h-\243\170\188\161\202\238/d\r\177\254\208\180\173Q\NAKb\247\197M\132\234v\222\188")))

-- Pending: bytestring constant; postulated builtin `bls12-381-G2-compress`; postulated builtin `bls12-381-G2-scalarMul`; postulated builtin `bls12-381-G2-add`; postulated builtin `bls12-381-G2-uncompress`.
pending-muladd : Set
pending-muladd = Pending (evalRaw test-muladd ≡ expected-muladd)
```

## mulneg-44

```
-- builtin/semantics/bls12_381_G2_scalarMul/mulneg-44
-- Multiplying a random point in G2 by the scalar -44 gives the expected result.
test-mulneg-44 : Untyped
test-mulneg-44 = (UApp (UBuiltin bls12-381-G2-compress) (UApp (UApp (UBuiltin bls12-381-G2-scalarMul) (UCon (tagCon integer (ℤ.negsuc 43)))) (UApp (UBuiltin bls12-381-G2-uncompress) (UCon (tagCon bytestring (mkByteString "\131\DLE\188\151\252z\217\177anQ\"ljR\ESC\157\DEL\223\ETX\247)\152\&3\230\162\b\174\ETX\153\254\199`E\164<\238\248F\224\149\141\f\223\ENQ\207+\US\NULF\SO\230\237\210w\139A>\183\194r\188[\148\209+\145\SI\138\196\235\ESCU\229\n\147dG\DC4xt\ETB\188F#I\197\224\246\243W\185\172\&2&*"))))))

expected-mulneg-44 : Result
expected-mulneg-44 = success (UCon (tagCon bytestring (mkByteString "\138*\149\188\153\&6\198\USP9\204o\187\224\226_\168\177R\142\161\140[\224\156\147\237\148\GS\FS\144RYp\134\184\211\179\181\251\189\DC1\f\227\137\&7\140T\DC4\239\211\DLE\222! \167\239\186\175p\208\US[\128\131Q\CAN\193\243\154Bs\161\SI\US*J\240\237\&3\167\193\DEL\186L\142?|\176\138\GS\151\232-V\DC1")))

-- Pending: bytestring constant; postulated builtin `bls12-381-G2-compress`; postulated builtin `bls12-381-G2-scalarMul`; postulated builtin `bls12-381-G2-uncompress`.
pending-mulneg-44 : Set
pending-mulneg-44 = Pending (evalRaw test-mulneg-44 ≡ expected-mulneg-44)
```

## mulperiodic-01

```
-- builtin/semantics/bls12_381_G2_scalarMul/mulperiodic-01
-- Scalar multiplication by the group size should give you the zero element of the group.
test-mulperiodic-01 : Untyped
test-mulperiodic-01 = (UApp (UApp (UBuiltin equalsByteString) (UApp (UBuiltin bls12-381-G2-compress) (UApp (UApp (UBuiltin bls12-381-G2-scalarMul) (UCon (tagCon integer (ℤ.pos 52435875175126190479447740508185965837690552500527637822603658699938581184513)))) (UApp (UBuiltin bls12-381-G2-uncompress) (UCon (tagCon bytestring (mkByteString "\176b\159\161\NAK\140-#\161\EOT\DC3\254\145\211\129\168M%\227\GS\EOT\FS\208\&7}%\130\132\152\253\STX\SOH\ESC5\137\&98\206\217u59^H\NAK \RSg\DLE\139\205Fe\224\219%\214\STX\215o\167\145\250\183\ACK\197J\191^\SUB\158D\180\172\RSk\173\243\210\172\ETX(\245\227\v\227Ag|\139\172]\218v\130\241"))))))) (UCon (tagCon bytestring (mkByteString "\192\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL"))))

expected-mulperiodic-01 : Result
expected-mulperiodic-01 = success (UCon (tagCon bool true))

-- Pending: bytestring constant; postulated builtin `equalsByteString`; postulated builtin `bls12-381-G2-compress`; postulated builtin `bls12-381-G2-scalarMul`; postulated builtin `bls12-381-G2-uncompress`.
pending-mulperiodic-01 : Set
pending-mulperiodic-01 = Pending (evalRaw test-mulperiodic-01 ≡ expected-mulperiodic-01)
```

## mulperiodic-02

```
-- builtin/semantics/bls12_381_G2_scalarMul/mulperiodic-02
-- Scalar multiplication should be periodic modulo the group size
test-mulperiodic-02 : Untyped
test-mulperiodic-02 = (UApp (UApp (UBuiltin bls12-381-G2-equal) (UApp (UApp (UBuiltin bls12-381-G2-scalarMul) (UApp (UApp (UBuiltin addInteger) (UCon (tagCon integer (ℤ.pos 123)))) (UCon (tagCon integer (ℤ.pos 52435875175126190479447740508185965837690552500527637822603658699938581184513))))) (UApp (UBuiltin bls12-381-G2-uncompress) (UCon (tagCon bytestring (mkByteString "\176b\159\161\NAK\140-#\161\EOT\DC3\254\145\211\129\168M%\227\GS\EOT\FS\208\&7}%\130\132\152\253\STX\SOH\ESC5\137\&98\206\217u59^H\NAK \RSg\DLE\139\205Fe\224\219%\214\STX\215o\167\145\250\183\ACK\197J\191^\SUB\158D\180\172\RSk\173\243\210\172\ETX(\245\227\v\227Ag|\139\172]\218v\130\241")))))) (UApp (UApp (UBuiltin bls12-381-G2-scalarMul) (UCon (tagCon integer (ℤ.pos 123)))) (UApp (UBuiltin bls12-381-G2-uncompress) (UCon (tagCon bytestring (mkByteString "\176b\159\161\NAK\140-#\161\EOT\DC3\254\145\211\129\168M%\227\GS\EOT\FS\208\&7}%\130\132\152\253\STX\SOH\ESC5\137\&98\206\217u59^H\NAK \RSg\DLE\139\205Fe\224\219%\214\STX\215o\167\145\250\183\ACK\197J\191^\SUB\158D\180\172\RSk\173\243\210\172\ETX(\245\227\v\227Ag|\139\172]\218v\130\241"))))))

expected-mulperiodic-02 : Result
expected-mulperiodic-02 = success (UCon (tagCon bool true))

-- Pending: bytestring constant; postulated builtin `bls12-381-G2-equal`; postulated builtin `bls12-381-G2-scalarMul`; postulated builtin `bls12-381-G2-uncompress`.
pending-mulperiodic-02 : Set
pending-mulperiodic-02 = Pending (evalRaw test-mulperiodic-02 ≡ expected-mulperiodic-02)
```

## mulperiodic-03

```
-- builtin/semantics/bls12_381_G2_scalarMul/mulperiodic-03
-- Scalar multiplication should be periodic modulo the group size
test-mulperiodic-03 : Untyped
test-mulperiodic-03 = (UApp (UApp (UBuiltin bls12-381-G2-equal) (UApp (UApp (UBuiltin bls12-381-G2-scalarMul) (UApp (UApp (UBuiltin addInteger) (UCon (tagCon integer (ℤ.pos 123)))) (UApp (UApp (UBuiltin multiplyInteger) (UCon (tagCon integer (ℤ.pos 987654321)))) (UCon (tagCon integer (ℤ.pos 52435875175126190479447740508185965837690552500527637822603658699938581184513)))))) (UApp (UBuiltin bls12-381-G2-uncompress) (UCon (tagCon bytestring (mkByteString "\176b\159\161\NAK\140-#\161\EOT\DC3\254\145\211\129\168M%\227\GS\EOT\FS\208\&7}%\130\132\152\253\STX\SOH\ESC5\137\&98\206\217u59^H\NAK \RSg\DLE\139\205Fe\224\219%\214\STX\215o\167\145\250\183\ACK\197J\191^\SUB\158D\180\172\RSk\173\243\210\172\ETX(\245\227\v\227Ag|\139\172]\218v\130\241")))))) (UApp (UApp (UBuiltin bls12-381-G2-scalarMul) (UCon (tagCon integer (ℤ.pos 123)))) (UApp (UBuiltin bls12-381-G2-uncompress) (UCon (tagCon bytestring (mkByteString "\176b\159\161\NAK\140-#\161\EOT\DC3\254\145\211\129\168M%\227\GS\EOT\FS\208\&7}%\130\132\152\253\STX\SOH\ESC5\137\&98\206\217u59^H\NAK \RSg\DLE\139\205Fe\224\219%\214\STX\215o\167\145\250\183\ACK\197J\191^\SUB\158D\180\172\RSk\173\243\210\172\ETX(\245\227\v\227Ag|\139\172]\218v\130\241"))))))

expected-mulperiodic-03 : Result
expected-mulperiodic-03 = success (UCon (tagCon bool true))

-- Pending: bytestring constant; postulated builtin `bls12-381-G2-equal`; postulated builtin `bls12-381-G2-scalarMul`; postulated builtin `bls12-381-G2-uncompress`.
pending-mulperiodic-03 : Set
pending-mulperiodic-03 = Pending (evalRaw test-mulperiodic-03 ≡ expected-mulperiodic-03)
```

## mulperiodic-04

```
-- builtin/semantics/bls12_381_G2_scalarMul/mulperiodic-04
-- Scalar multiplication should be periodic modulo the group size
test-mulperiodic-04 : Untyped
test-mulperiodic-04 = (UApp (UApp (UBuiltin bls12-381-G2-equal) (UApp (UApp (UBuiltin bls12-381-G2-scalarMul) (UApp (UApp (UBuiltin addInteger) (UCon (tagCon integer (ℤ.pos 123)))) (UApp (UApp (UBuiltin multiplyInteger) (UCon (tagCon integer (ℤ.negsuc 987654320)))) (UCon (tagCon integer (ℤ.pos 52435875175126190479447740508185965837690552500527637822603658699938581184513)))))) (UApp (UBuiltin bls12-381-G2-uncompress) (UCon (tagCon bytestring (mkByteString "\176b\159\161\NAK\140-#\161\EOT\DC3\254\145\211\129\168M%\227\GS\EOT\FS\208\&7}%\130\132\152\253\STX\SOH\ESC5\137\&98\206\217u59^H\NAK \RSg\DLE\139\205Fe\224\219%\214\STX\215o\167\145\250\183\ACK\197J\191^\SUB\158D\180\172\RSk\173\243\210\172\ETX(\245\227\v\227Ag|\139\172]\218v\130\241")))))) (UApp (UApp (UBuiltin bls12-381-G2-scalarMul) (UCon (tagCon integer (ℤ.pos 123)))) (UApp (UBuiltin bls12-381-G2-uncompress) (UCon (tagCon bytestring (mkByteString "\176b\159\161\NAK\140-#\161\EOT\DC3\254\145\211\129\168M%\227\GS\EOT\FS\208\&7}%\130\132\152\253\STX\SOH\ESC5\137\&98\206\217u59^H\NAK \RSg\DLE\139\205Fe\224\219%\214\STX\215o\167\145\250\183\ACK\197J\191^\SUB\158D\180\172\RSk\173\243\210\172\ETX(\245\227\v\227Ag|\139\172]\218v\130\241"))))))

expected-mulperiodic-04 : Result
expected-mulperiodic-04 = success (UCon (tagCon bool true))

-- Pending: bytestring constant; postulated builtin `bls12-381-G2-equal`; postulated builtin `bls12-381-G2-scalarMul`; postulated builtin `bls12-381-G2-uncompress`.
pending-mulperiodic-04 : Set
pending-mulperiodic-04 = Pending (evalRaw test-mulperiodic-04 ≡ expected-mulperiodic-04)
```
