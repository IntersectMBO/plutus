```
module Algorithmic.Properties where
```

## Imports

```
open import Relation.Binary.HeterogeneousEquality using (_≅_;refl)
open import Relation.Binary.PropositionalEquality using (_≡_;refl)
open import Data.Product using (_×_;∃) renaming (_,_ to _,,_)

open import Utils using (*)
open import Type using (∅;_,⋆_)
open import Type.BetaNormal using (_⊢Nf⋆_)
open _⊢Nf⋆_
open import Algorithmic using (_⊢_;∅)
open import Type.BetaNBE.RenamingSubstitution using (_[_]Nf)
```

## Pragmas

```
```

## Some syntactic lemmas

```
lem-·⋆ : ∀{K K'}{A : ∅ ⊢Nf⋆ K}{A' : ∅ ⊢Nf⋆ K'}{B : ∅ ,⋆ K ⊢Nf⋆ *}{B' : ∅ ,⋆ K' ⊢Nf⋆ *}
  → ∀{M : ∅ ⊢ Π B}{M' : ∅ ⊢ Π B'}
  → ∀{C}(p : C ≡ B [ A ]Nf)(p' : C ≡ B' [ A' ]Nf)
  → M' _⊢_.·⋆ A' / p' ≡ M _⊢_.·⋆ A / p
  → ∃ λ (p : K ≡ K') → M' ≅ M × A ≅ A' × B ≅ B'
lem-·⋆ p .p refl = refl ,, refl ,, refl ,, refl

lem-unwrap : ∀{K K'}{A}{A'}{B : ∅ ⊢Nf⋆ K}{B' : ∅ ⊢Nf⋆ K'}
  → ∀{M : ∅ ⊢ μ A B}{M' : ∅ ⊢ μ A' B'}{C}
  → {p : C ≡ _}{q : C ≡ _}
  → _⊢_.unwrap M p ≡ _⊢_.unwrap M' q
  → K ≡ K' × A ≅ A' × B ≅ B' × M ≅ M'
lem-unwrap refl = refl ,, refl ,, refl ,, refl
```
