# CEK behavioural equivalence with CK machine

```
module Algorithmic.BehaviouralEquivalence.CKvsCEK where

open import Data.Nat using (suc)
open import Data.Empty using (⊥-elim)
open import Data.Product using (∃)
open import Data.List using ([];_∷_)
open import Relation.Binary.PropositionalEquality using (_≡_;refl;sym;cong;trans) 
                                                  renaming (subst to substEq)
open import Data.Product using (_×_;Σ) renaming (_,_ to _,,_)
open import Data.Sum using (_⊎_;inj₁;inj₂)
open import Type using (Ctx⋆;∅;_,⋆_)
open import Type.BetaNormal using (_⊢Nf⋆_;_⊢Ne⋆_)
open _⊢Nf⋆_
open _⊢Ne⋆_
open import Type.BetaNBE.RenamingSubstitution using (_[_]Nf;subNf-id)
open import Algorithmic using (Ctx;_⊢_;_∋_;conv⊢;builtin_/_)
open Ctx
open _⊢_
open _∋_
open import Algorithmic.Signature using (SigTy;btype)
open SigTy
open import Builtin using (signature)
open import Builtin.Signature using (Sig;args♯)
open Sig
open import Algorithmic.RenamingSubstitution using (Sub;sub;exts;exts⋆;_[_];_[_]⋆)
open import Utils hiding (TermCon)

open import Builtin.Constant.Type Ctx⋆ (_⊢Nf⋆ *) using (TyCon)
open TyCon

open import Builtin.Constant.Term Ctx⋆ Kind * _⊢Nf⋆_ con using (TermCon)
open TermCon

open import Algorithmic.CEK
import Algorithmic.ReductionEC as Red
import Algorithmic.CK as CK
import Algorithmic.BehaviouralEquivalence.CCvsCK as CK
import Algorithmic.CC as CC
open import Algorithmic.ReductionEC using () renaming (red2cekVal to ck2cekVal)
-- convert CK things to CEK things

ck2cekFrame : ∀{A B} → Red.Frame A B → Frame A B
ck2cekFrame (Red.-· M) = -· M []
ck2cekFrame (VM Red.·-) = ck2cekVal VM ·-
ck2cekFrame (Red.-·⋆ A) = -·⋆ A
ck2cekFrame Red.wrap- = wrap-
ck2cekFrame Red.unwrap- = unwrap-

ck2cekStack : ∀{A B} → CK.Stack A B → Stack A B
ck2cekStack CK.ε = ε
ck2cekStack (s CK., f) = ck2cekStack s , ck2cekFrame f

ck2cekState : ∀{A} → CK.State A → State A
ck2cekState (s CK.▻ L) = ck2cekStack s ; [] ▻ L
ck2cekState (s CK.◅ V) = ck2cekStack s ◅ ck2cekVal V
ck2cekState (CK.□ V) = □ (ck2cekVal V)
ck2cekState (CK.◆ A) = ◆ A

-- convert CEK things to CK things

cek2ckVal : ∀{A} → (V : Value A) → Red.Value (discharge V)

cek2ckBApp : ∀{b}
   {tn tm}{pt : tn ∔ tm ≣ fv♯ (signature b)}
   {an am}{pa : an ∔ am ≣ args♯ (signature b)}
   {A}{σA : SigTy pt pa A}
  → (vs : BApp b A σA) → Red.BApp b σA (dischargeB vs)
cek2ckBApp base = Red.base
cek2ckBApp (app vs v) = Red.step (cek2ckBApp vs) (cek2ckVal v)
cek2ckBApp (app⋆ vs refl refl) = Red.step⋆ (cek2ckBApp vs) refl refl

cek2ckVal (V-ƛ M ρ) = Red.V-ƛ _
cek2ckVal (V-Λ M ρ) = Red.V-Λ _
cek2ckVal (V-wrap V) = Red.V-wrap (cek2ckVal V)
cek2ckVal (V-con cn) = Red.V-con cn
cek2ckVal (V-I⇒ b x) = Red.V-I⇒ b (cek2ckBApp x)
cek2ckVal (V-IΠ b x) = Red.V-IΠ b (cek2ckBApp x)

cek2ckClos : ∀{A Γ} → Γ ⊢ A → Env Γ → ∅ ⊢ A
-- cek2ckClos L ρ = conv⊢ refl (subNf-id _) (sub (ne ∘ `) (env2sub ρ) L)
cek2ckClos (` x) ρ = discharge (lookup x ρ)
cek2ckClos (ƛ L) ρ = ƛ (dischargeBody L ρ)
cek2ckClos (L · M) ρ = cek2ckClos L ρ · cek2ckClos M ρ
cek2ckClos (Λ L) ρ = Λ (dischargeBody⋆ L ρ)
cek2ckClos (L ·⋆ A / refl) ρ = cek2ckClos L ρ ·⋆ A / refl
cek2ckClos (wrap A B L) ρ = wrap A B (cek2ckClos L ρ)
cek2ckClos (unwrap L refl) ρ = unwrap (cek2ckClos L ρ) refl
cek2ckClos (con c) ρ = con c
cek2ckClos (builtin b / refl) ρ = builtin b / refl
cek2ckClos (error _) ρ = error _

cek2ckFrame : ∀{A B} → Frame A B → Red.Frame A B
cek2ckFrame (-· N ρ) = Red.-· cek2ckClos N ρ
cek2ckFrame (V ·-) = cek2ckVal V Red.·-
cek2ckFrame (-·⋆ A) = Red.-·⋆ A
cek2ckFrame wrap- = Red.wrap-
cek2ckFrame unwrap- = Red.unwrap-

cek2ckStack : ∀{A B} → Stack A B → CK.Stack A B
cek2ckStack ε = CK.ε
cek2ckStack (s , f) = cek2ckStack s CK., cek2ckFrame f
 
cek2ckState : ∀{A} → State A → CK.State A
cek2ckState (s ; ρ ▻ L) = cek2ckStack s CK.▻ cek2ckClos L ρ
cek2ckState (s ◅ V) = cek2ckStack s CK.◅ cek2ckVal V
cek2ckState (□ V) = CK.□ (cek2ckVal V)
cek2ckState (◆ A) = CK.◆ A

data _-→s_ {A : ∅ ⊢Nf⋆ *} : State A → State A → Set where
  base  : {s : State A} → s -→s s
  step* : {s s' s'' : State A}
        → step s ≡ s'
        → s' -→s s''
        → s -→s s''

step** : ∀{A}{s : State A}{s' : State A}{s'' : State A}
        → s -→s s'
        → s' -→s s''
        → s -→s s''
step** base q = q
step** (step* x p) q = step* x (step** p q)

-- some syntactic assumptions
{-
V-Ilem : ∀ {b}{A : ∅ ⊢Nf⋆ *}
       → ∀{tn tm} {pt : tn ∔ tm ≣ fv♯ (signature b)}
       → ∀{an am} {pa : an ∔ suc am ≣ args♯ (signature b)}
       → {σA : SigTy pt pa A}
       → {t : ∅ ⊢ A}
       → (bt : Red.BApp b σA t)
       → (p : discharge (V-I b (ck2cekBApp bt)) ≡ t)
       → Red.V-I b bt ≡ subst (cek2ckVal (V-I b (ck2cekBApp bt)))
V-Ilem bt = 
-}
postulate ival-lem : ∀ b {A}{s : CK.Stack A _} → (s CK.◅ Red.ival b) ≡ (s CK.◅ cek2ckVal (ival b))
--ival-lem b {s = s} = {! cong (λ z → s CK.◅ z)  !}

postulate dischargeBody-lem' : ∀{B}{Γ}{C}(M : Γ , C ⊢ B) ρ V → (dischargeBody M ρ [ CK.discharge (cek2ckVal V) ]) ≡ cek2ckClos M (ρ ∷ V)

{- proof sketch for dischargeBody-lem'

-- type level stuff omitted for simplicity below

dischargeBody M ρ [ discharge (cek2ckVal V) ]
= { def dischargeBody }
sub (exts (env2sub ρ)) M [ discharge (cek2ckVal V) ] 
= { def of [_] }
sub (sub-cons ` (discharge (cek2ckVal V)))
    (sub (exts (env2sub ρ)) (discharge (cek2ckVal V)))
    M
= { sub-comp (lemma required) }
sub (sub (sub-cons ` (discharge (cek2ckVal V))) ∘ (exts (env2sub ρ)))
    M
= {  }
sub (sub-cons (env2sub ρ) (discharge (cek2ckVal V))) M
= {  }
sub (env2sub (ρ ∷ V)) M
= { lemma required }
cek2ckClos M (ρ ∷ V)

-}

dischargeBody-lem : ∀{A B}{Γ}{C}{s : CK.Stack A B}(M : Γ , C ⊢ _) ρ V → (s CK.▻ (dischargeBody M ρ [ CK.discharge (cek2ckVal V) ])) ≡ (s CK.▻ cek2ckClos M (ρ ∷ V))
dischargeBody-lem M ρ V = cong (_ CK.▻_) (dischargeBody-lem' M ρ V)

postulate discharge-lem : ∀{A}(V : Value A) → Red.deval (cek2ckVal V) ≡ discharge V

postulate dischargeBody⋆-lem' : ∀{Γ K B A}(M : Γ ,⋆ K ⊢ B) ρ → dischargeBody⋆ M ρ [ A ]⋆ ≡ (cek2ckClos (M [ A ]⋆) ρ)

dischargeBody⋆-lem : ∀{Γ K B A C}{s : CK.Stack C _}(M : Γ ,⋆ K ⊢ B) ρ → (s CK.▻ (dischargeBody⋆ M ρ [ A ]⋆)) ≡ (s CK.▻ cek2ckClos (M [ A ]⋆) ρ)
dischargeBody⋆-lem M ρ = cong (_ CK.▻_) (dischargeBody⋆-lem' M ρ)

postulate dischargeB-lem : ∀ {A}{B : ∅ ,⋆ * ⊢Nf⋆ *}{C b}
                     {tn tm}{pt : tn ∔ suc tm ≣ fv♯ (signature b)}
                     {an am}{pa : an ∔ suc am ≣ args♯ (signature b)}
                     {σB : SigTy (bubble pt) pa B}
                     {x : BApp b (Π B) (sucΠ σB)} 
                  (s : CK.Stack C (B [ A ]Nf)) 
                → s CK.◅ Red.V-I b (Red.step⋆ (cek2ckBApp x) refl refl) ≡ (s CK.◅ cek2ckVal (V-I b (app⋆ x refl refl)))

postulate dischargeB'-lem : ∀ {A}{C b}
                    {tn tm}{pt : tn ∔ tm ≣ fv♯ (signature b)}
                     {an am}{pa : an ∔ suc am ≣ args♯ (signature b)}
                     {σA : SigTy pt pa A}
                     {x : BApp b A σA} 
                     (s : CK.Stack C _) 
                  → s CK.◅ Red.V-I b (cek2ckBApp x) ≡ (s CK.◅ cek2ckVal (V-I b x))

postulate dischargeB-lem' : ∀ {A}{b}
                  {tn tm}{pt : tn ∔ tm ≣ fv♯ (signature b)}
                    {an am}{pa : an ∔ suc am ≣ args♯ (signature b)}
                    {σA : SigTy pt pa A}
                    {x : BApp b A σA} 
                  → dischargeB x ≡ discharge (V-I b x)
                

postulate dischargeB-lem'' :  ∀ {A}{b}
                  {tn tm}{pt : tn ∔ tm ≣ fv♯ (signature b)}
                    {an am}{pa : an ∔ suc am ≣ args♯ (signature b)}
                    {σA : SigTy pt pa A}
                    {x : BApp b A σA} 
                  → substEq Red.Value dischargeB-lem' (Red.V-I b (cek2ckBApp x)) ≡ cek2ckVal (V-I b x)


-- assuming that builtins work the same way for CEK and red/CK

postulate BUILTIN-lem : ∀ b {A}
               {tn}{pt : tn ∔ 0 ≣ fv♯ (signature b)}
                {an}{pa : an ∔ 0 ≣ args♯ (signature b)}
                {σA : SigTy pt pa A}          
              → (q : BApp b A σA) 
              → Red.BUILTIN' b (cek2ckBApp q) ≡ cek2ckClos (BUILTIN' b q) []


thm65a : ∀{A}(s s' : State A) → s -→s s' → cek2ckState s CK.-→s cek2ckState s'
thm65a s s  base        = CK.base
thm65a (s ; ρ ▻ ` x) s' (step* refl q) = CK.step** (CK.lemV (discharge (lookup x ρ)) (cek2ckVal (lookup x ρ)) (cek2ckStack s)) (thm65a _ s' q)
thm65a (s ; ρ ▻ ƛ L) s' (step* refl q) = CK.step* refl (thm65a _ s' q)
thm65a (s ; ρ ▻ (L · M)) s' (step* refl q) = CK.step* refl (thm65a _ s' q)
thm65a (s ; ρ ▻ Λ L) s' (step* refl q) = CK.step* refl (thm65a _ s' q)
thm65a (s ; ρ ▻ (L ·⋆ A / refl)) s' (step* refl q) = CK.step* refl (thm65a _ s' q)
thm65a (s ; ρ ▻ wrap A B L) s' (step* refl q) = CK.step* refl (thm65a _ s' q)
thm65a (s ; ρ ▻ unwrap L refl) s' (step* refl q) = CK.step* refl (thm65a _ s' q)
thm65a (s ; ρ ▻ con c) s' (step* refl q) = CK.step* refl (thm65a _ s' q)
thm65a (s ; ρ ▻ (builtin b / refl)) s' (step* refl q) = CK.step* (ival-lem b) (thm65a _ s' q)
thm65a (s ; ρ ▻ error _) s' (step* refl q) = CK.step* refl (thm65a _ s' q)
thm65a (ε ◅ V) s' (step* refl q) = CK.step* refl (thm65a _ s' q)
thm65a ((s , -· L ρ) ◅ V) s' (step* refl q) = CK.step* refl (thm65a _ s' q)
thm65a ((s , (V-ƛ M ρ ·-)) ◅ V) s' (step* refl q)    = CK.step*
  (dischargeBody-lem M ρ V)
  (thm65a _ s' q)
thm65a ((s , (V-I⇒ b {am = 0} x ·-)) ◅ V) s' (step* refl q) = CK.step*
  (cong (cek2ckStack s CK.▻_) (BUILTIN-lem b (app x V)))
  (thm65a _ s' q)
thm65a ((s , (V-I⇒ b {am = suc _} x ·-)) ◅ V) s' (step* refl q) = CK.step* (dischargeB'-lem (cek2ckStack s)) (thm65a _ s' q)
thm65a ((s , -·⋆ A) ◅ V-Λ M ρ) s' (step* refl q) = CK.step* (dischargeBody⋆-lem M ρ) (thm65a _ s' q)
thm65a ((s , -·⋆ A) ◅ V-IΠ b x) s' (step* refl q) = CK.step* (dischargeB-lem (cek2ckStack s)) (thm65a _ s' q)
thm65a ((s , wrap-) ◅ V) s' (step* refl q) = CK.step* refl (thm65a _ s' q)
thm65a ((s , unwrap-) ◅ V-wrap V) s' (step* refl q) = CK.step* (cong (cek2ckStack s CK.▻_) (discharge-lem V)) (CK.step** (CK.lemV _ (cek2ckVal V) (cek2ckStack s)) (thm65a _ s' q))
thm65a (□ V) s' (step* refl q) = CK.step* refl (thm65a _ s' q)
thm65a (◆ A) s' (step* refl q) = CK.step* refl (thm65a _ s' q)


postulate clos-lem : ∀{A}(M : ∅ ⊢ A) → M ≡ cek2ckClos M []

lem□ : ∀{A}(W V : Value A) → □ W -→s □ V → W ≡ V
lem□ W .W base = refl
lem□ W V (step* refl p) = lem□ W V p

-- the below lemmas/assumptions consider the case that where M is a
--  variable in M' == clos M ρ, but I am not sure if these cases ever
--  occur when the CEK machine is in value mode. This may be overkill
--  for our machine, in the textbook there is not such a clear
--  distinction between term and value mode and this analysis is needed.

-- note N cannot be a variable because if it was then the result of
-- the lookup in ρ would be a value that is then discharged which
-- couldn't be an application as applications are not values
postulate cek2ckClos-·lem : ∀{A B}{L : ∅ ⊢ A ⇒ B}{M : ∅ ⊢ A}{Γ}{ρ : Env Γ}{N : Γ ⊢ B} → L · M ≡ cek2ckClos N ρ → ∃ λ L' → ∃ λ M' → N ≡ L' · M' × L ≡ cek2ckClos L' ρ × M ≡ cek2ckClos M' ρ

-- as ƛ is a value, it can be the result of a variable lookup
postulate cek2ckClos-ƛlem : ∀{A B}{L : ∅ , A ⊢ B}{Γ}{ρ : Env Γ}{N : Γ ⊢ A ⇒ B} → (p : ƛ L ≡ cek2ckClos N ρ) → (∃ λ L' → N ≡ ƛ L' × L ≡ dischargeBody L' ρ) ⊎ ∃ λ x → N ≡ ` x × ∃ λ (p : ƛ L ≡ discharge (lookup x ρ)) → substEq Red.Value p (Red.V-ƛ L) ≡ cek2ckVal (lookup x ρ)

postulate cek2ckClos-·⋆lem : ∀{K B}{L : ∅ ⊢ Π B}{A : ∅ ⊢Nf⋆ K}{Γ}{ρ : Env Γ}{N : Γ ⊢ B [ A ]Nf} → L ·⋆ A / refl ≡ cek2ckClos N ρ → ∃ λ L' → N ≡ L' ·⋆ A / refl × L ≡ cek2ckClos L' ρ

postulate cek2ckClos-Λlem : ∀{K B}{L : ∅ ,⋆ K ⊢ B}{Γ}{ρ : Env Γ}{N : Γ ⊢ Π B} → (p : Λ L ≡ cek2ckClos N ρ) → (∃ λ L' → N ≡ Λ L' × L ≡ dischargeBody⋆ L' ρ) ⊎ ∃ λ x → N ≡ ` x × ∃ λ (p : Λ L ≡ discharge (lookup x ρ)) → substEq Red.Value p (Red.V-Λ L) ≡ cek2ckVal (lookup x ρ)

postulate cek2ckClos-wraplem : ∀{K}{A}{B : ∅ ⊢Nf⋆ K}{L}{Γ}{ρ : Env Γ}{N : Γ ⊢ μ A B} → (p : wrap A B L ≡ cek2ckClos N ρ) → (∃ λ L' → N ≡ wrap A B L' × L ≡ cek2ckClos L' ρ) ⊎ ∃ λ x → N ≡ ` x × ∃ λ V → ∃ λ (q : V-wrap V ≡ lookup x ρ) → discharge V ≡ L × substEq Red.Value (cong discharge q) (Red.V-wrap (cek2ckVal V)) ≡ cek2ckVal (lookup x ρ)

postulate cek2ckClos-unwraplem : ∀{K}{A}{B : ∅ ⊢Nf⋆ K}{L : ∅ ⊢ μ A B}{Γ}{ρ : Env Γ}{N : Γ ⊢ _} → (p : unwrap L refl ≡ cek2ckClos N ρ) → (∃ λ L' → N ≡ unwrap L' refl × L ≡ cek2ckClos L' ρ)

postulate cek2ckClos-conlem : ∀{tc : TyCon ∅}(c : TermCon (con tc)){Γ}{M' : Γ ⊢ con tc}{ρ : Env Γ} → con c ≡ cek2ckClos M' ρ → M' ≡ con c ⊎ ∃ λ x → M' ≡ ` x × V-con c ≡ lookup x ρ

postulate cek2ckClos-ibuiltinlem : ∀{b}{Γ}{M' : Γ ⊢ btype b}{ρ : Env Γ} → builtin b / refl ≡ cek2ckClos M' ρ → (M' ≡ builtin b / refl × ∃ λ p → substEq Red.Value p (Red.ival b) ≡ cek2ckVal (ival b)) ⊎ ∃ λ x → M' ≡ ` x × ∃ λ (p : builtin b / refl ≡ discharge (lookup x ρ)) → substEq Red.Value p (Red.ival b) ≡ cek2ckVal (lookup x ρ)

cek2ckStack-εlem : ∀{A}(s : Stack A A) → CK.ε ≡ cek2ckStack s → s ≡ ε
cek2ckStack-εlem ε       p = refl
cek2ckStack-εlem (s , f) ()

cek2ckStack-,lem : ∀{A B C}(s : CK.Stack A B)(s' : Stack A C)(f : Red.Frame B C)
  → s CK., f ≡ cek2ckStack s' →
  ∃ λ (s'' : Stack A B) → ∃ λ (f' : Frame B C) → s' ≡ (s'' Stack., f')
  × s ≡ cek2ckStack s'' × f ≡ cek2ckFrame f'
cek2ckStack-,lem _ (s' , f) _ refl =
  _ ,, _ ,, refl ,, refl ,, refl

cek2ckFrame-·-lem : ∀{A B} f {M : ∅ ⊢ A ⇒ B}(W : Red.Value M)
  → W Red.·- ≡ cek2ckFrame f →
  ∃ λ W' → f ≡ (W' ·-) × ∃ λ (p : M ≡ discharge W') → substEq Red.Value p W ≡ cek2ckVal W'
cek2ckFrame-·-lem (x ·-) .(cek2ckVal x) refl = _ ,, refl ,, refl ,, refl

postulate cek2ckFrame--·lem : ∀{A B}(f : Frame B (A ⇒ B)){M : ∅ ⊢ A} → (Red.-· M) ≡ cek2ckFrame f → ∃ λ Γ → ∃ λ (M' : Γ ⊢ A) → ∃ λ (ρ : Env Γ) → f ≡ (-· M' ρ) × M ≡ cek2ckClos M' ρ

postulate cek2ckFrame--·⋆lem : ∀{K A}{B : ∅ ,⋆ K ⊢Nf⋆ *}(f : Frame (B [ A ]Nf) (Π B)) → Red.-·⋆ A ≡ cek2ckFrame f → f ≡ -·⋆ A
   
postulate cek2ckFrame-unwrap-lem : ∀{K}{A}{B : ∅ ⊢Nf⋆ K}(f : Frame _ (μ A B)) → Red.unwrap- {A = A}{B = B} ≡ cek2ckFrame f → f ≡ unwrap-

postulate cek2ckFrame-wrap-lem : ∀{K}{A}{B : ∅ ⊢Nf⋆ K}(f : Frame (μ A B) _) → Red.wrap- {A = A}{B = B} ≡ cek2ckFrame f → f ≡ wrap-

thm65bV : ∀{A B}{L : ∅ ⊢ A}{M}{s : CK.Stack A B}{V : Red.Value L}
  {W : Red.Value M}{W'}{s'}
  → (p : M ≡ discharge W')
  → substEq Red.Value p W ≡ cek2ckVal W'
  → s ≡ cek2ckStack s'
  → (s CK.◅ W) CK.-→s CK.□ V
  → ∃ λ V' → ((s' ◅ W') -→s □ V') × ∃ λ p → cek2ckVal V' ≡ substEq Red.Value p V

substLem : {A : Set}(P : A → Set){a a' : A}(p q : a ≡ a')(x : P a) →
  substEq P p x ≡ substEq P q x
substLem P refl refl x = refl

postulate fast-forward : ∀{A B}(s : CK.Stack A B)(s' : CK.State A)(M : ∅ ⊢ B)
                 → (V : Red.Value M)
                 → (s CK.▻ M) CK.-→s s' → (s CK.◅ V) CK.-→s s'

{-# TERMINATING #-}
-- this is needed as in the wrap case we fast-forward the CK machine state
-- and recurse on something which is quite a bit shorter

thm65b : ∀{A B}{L : ∅ ⊢ A}{Γ M}{s : CK.Stack A B}{V : Red.Value L}
  {M'}{ρ : Env Γ}{s'}
  → M ≡ cek2ckClos M' ρ
  → s ≡ cek2ckStack s'
  → (s CK.▻ M) CK.-→s CK.□ V
  → ∃ λ V' → ((s' ; ρ ▻ M') -→s □ V') × ∃ λ p → cek2ckVal V' ≡ substEq Red.Value p V
thm65b {M = ƛ M} {s = s} {M' = N} {ρ} {s'} p q (CK.step* refl r)
  with cek2ckClos-ƛlem {ρ = ρ}{N = N} p
thm65b {M = ƛ M} {s = s} {M' = N} {ρ} {s'} refl q (CK.step* refl r) | inj₁ (L' ,, refl ,, z) with thm65bV refl refl q r
... | V ,, r' ,, y ,, y' = V ,, step* refl r' ,, y ,, y'
thm65b {Γ = _} {ƛ M} {s = s} {M' = .(` x)} {ρ} {s'} p q (CK.step* refl r) | inj₂ (x ,, refl ,, y' ,, y'') with thm65bV p (trans (substLem Red.Value p y' _) y'') q r
... | V ,, r' ,, y ,, y' = V ,, step* refl r' ,, y ,, y'
thm65b {M = L · M} {s = s} {M' = N}{ρ}{s'} p q (CK.step* refl r)
  with cek2ckClos-·lem {ρ = ρ}{N = N} p
... | L' ,, M' ,, refl ,, Lp ,, refl
  with thm65b Lp (cong (CK._, (Red.-· M)) q) r
... | x ,, y ,, z  ,, z' = x ,, step* refl y ,, z ,, z'
thm65b {M = Λ M} {s = s}{M' = N}{ρ}{s'} p q (CK.step* refl r)
  with cek2ckClos-Λlem {ρ = ρ}{N = N} p
thm65b {M' = .(Λ L')} {ρ} {s'} refl q (CK.step* refl r) | inj₁ (L' ,, refl ,, z) with thm65bV refl refl q r
... | V ,, r' ,, y ,, y' = V ,, step* refl r' ,, y ,, y'
thm65b {M = Λ M} {s = s}{M' = N}{ρ}{s'} p q (CK.step* refl r) | inj₂ (x ,, refl ,, y' ,, y'') with thm65bV p (trans (substLem Red.Value p y' _) y'') q r
... | V ,, r' ,, y ,, y' = V ,, step* refl r' ,, y ,, y'
thm65b {M = M ·⋆ A / refl} {s = s}{M' = N}{ρ}{s' = s'} p q (CK.step* refl r)
  with cek2ckClos-·⋆lem {ρ = ρ}{N = N} p
... | L' ,, refl ,, y'
  with thm65b y' (cong (CK._, (Red.-·⋆ A)) q) r
... | x ,, y ,, z ,, z' = x ,, step* refl y ,, z ,, z'
thm65b {M = wrap A B M} {s = s}{M' = N}{ρ}{s' = s'} p q (CK.step* refl r)
  with cek2ckClos-wraplem {ρ = ρ}{N = N} p
thm65b {M = wrap A B M} {s = s}{M' = N}{ρ}{s' = s'} p refl r | inj₂ (x ,, refl ,, W ,, y1 ,, refl ,, y3) with thm65bV (cong discharge y1) y3 refl (fast-forward _ _ _ (cek2ckVal (V-wrap W)) r)
... | V ,, r' ,, z ,, z' = V ,, step* refl r' ,, z ,, z'
thm65b {Γ = _} {wrap _ _ .(cek2ckClos V ρ)} {s = s} {M' = .(wrap _ _ V)} {ρ} {s' = s'} refl refl (CK.step* refl r) | inj₁ (V ,, refl ,, y) with thm65b refl refl r
... | x ,, y ,, z ,, z' = x ,, step* refl y ,, z ,, z'

thm65b {M = unwrap M refl} {s = s}{M' = N}{ρ = ρ} {s' = s'} p q (CK.step* refl r)
  with cek2ckClos-unwraplem {ρ = ρ}{N = N} p
... | L' ,, refl ,, x2 with thm65b x2 (cong (CK._, Red.unwrap-) q) r
... | V' ,, r' ,, y1 ,, y2 = _ ,, step* refl r' ,, y1 ,, y2
thm65b {M = con c}{s = s}{M' = M'}{ρ = ρ}{s' = s'} p q (CK.step* refl r)
  with thm65bV refl refl q r
... | W ,, r' ,, x1 ,, x2
  with cek2ckClos-conlem c {M' = M'}{ρ = ρ} p
... | inj₁ refl = _ ,, step* refl r' ,, x1 ,, x2
... | inj₂ (var ,, refl ,, y2) = _ ,, step* (cong (s' ◅_) (sym y2)) r' ,, x1 ,, x2

thm65b {M = builtin b / refl} {s = s}{M' = N}{ρ = ρ}{s' = s'} p q (CK.step* refl r)
  with cek2ckClos-ibuiltinlem {M' = N}{ρ = ρ} p
thm65b {M = builtin b / refl} {s = s}{M' = N}{ρ = ρ}{s' = s'} p q (CK.step* refl r) | inj₂ (x ,, refl ,, y2 ,, y3) with thm65bV y2 y3 q r
... | V' ,, r' ,, y1 ,, y2 = V' ,, step* refl r' ,, y1 ,, y2
thm65b {M = builtin b / refl} {s = s}{M' = N}{ρ = ρ}{s' = s'} p q (CK.step* refl r) | inj₁ (refl ,, x1 ,, x2)
  with thm65bV x1 x2 q r
... | V' ,, r' ,, y1 ,, y2 = V' ,, step* refl r' ,, y1 ,, y2

thm65b {M = error _} {s = s} {s' = s'} p q (CK.step* refl r) = ⊥-elim (CK.lem◆' _ r)

thm65bV {s = CK.ε} {W = W} {s' = s'} refl refl r (CK.step* refl x)
  rewrite cek2ckStack-εlem s' r
  with CK.lem□ _ _ x
... | refl ,, refl = _ ,, step* refl base ,, refl ,, refl
thm65bV {s = s CK., (Red.-· x₁)} {W = W} {s' = s'} refl refl r (CK.step* refl x)
  with cek2ckStack-,lem _ _ _ r
... | _ ,, _ ,, refl ,, refl ,, z1
  with cek2ckFrame--·lem _ z1
... | Γ ,, M' ,, ρ ,, refl ,, z2
  with thm65b z2 refl x
... | _ ,, x' ,, refl ,, refl = _ ,, step* refl x' ,, refl ,, refl
thm65bV {s = s CK., (x₁ Red.·-)} {W = W} {s' = s'} p q r (CK.step* refl x)
  with cek2ckStack-,lem _ _ _ r
... | _ ,, _ ,, refl ,, refl ,, z1
  with cek2ckFrame-·-lem _ _ z1
thm65bV {M = _} {.(cek2ckStack fst) CK., (.(cek2ckVal (V-ƛ M x₁)) Red.·-)} {W = W} {_} {.(fst , (V-ƛ M x₁ ·-))} refl refl r (CK.step* refl x) | fst ,, .(V-ƛ M x₁ ·-) ,, refl ,, refl ,, z1 | V-ƛ M x₁ ,, refl ,, refl ,, refl
  with thm65b (dischargeBody-lem' M x₁ _) refl x
... | V'' ,, x' ,, refl ,, refl = _ ,, step* refl x' ,, refl ,, refl
thm65bV {M = _} {.(cek2ckStack fst) CK., (.(cek2ckVal (V-I⇒ b x₁)) Red.·-)} {W = W} {_} {.(fst , (V-I⇒ b x₁ ·-))} refl refl r (CK.step* refl x) | fst ,, .(V-I⇒ b x₁ ·-) ,, refl ,, refl ,, z1 | V-I⇒ b {am = 0} x₁ ,, refl ,, refl ,, refl with thm65b (BUILTIN-lem b (app x₁ _)) refl x
... | V' ,, r' ,, y1 ,, y2 = V' ,, step* refl r' ,, y1 ,, y2
thm65bV {M = _} {.(cek2ckStack fst) CK., (.(cek2ckVal (V-I⇒ b x₁)) Red.·-)} {W = W} {_} {.(fst , (V-I⇒ b x₁ ·-))} refl refl r (CK.step* refl x) | fst ,, .(V-I⇒ b x₁ ·-) ,, refl ,, refl ,, z1 | V-I⇒ b {am = suc _} x₁ ,, refl ,, refl ,, refl with thm65bV dischargeB-lem'  dischargeB-lem'' refl x
... | V' ,, r' ,, y1 ,, y2 = V' ,, step* refl r' ,, y1 ,, y2
thm65bV {s = s CK., Red.-·⋆ A} {W = .(cek2ckVal (V-Λ M x₁))} {V-Λ M x₁} {s' = s'} refl refl r (CK.step* refl x)
  with cek2ckStack-,lem _ _ _ r
... | x1 ,, x2 ,, refl ,, z0 ,, z1
  with thm65b {M' = M [ A ]⋆}{ρ = x₁} (dischargeBody⋆-lem' M x₁) z0 x
... | f ,, x' ,, refl ,, z2
  with cek2ckFrame--·⋆lem x2 z1
... | refl = _ ,, step* refl x' ,, refl ,, z2
thm65bV {s = s CK., Red.-·⋆ A} {W = .(cek2ckVal (V-IΠ b x₁))} {V-IΠ b x₁} {s' = s'} refl refl r (CK.step* refl x)
  with cek2ckStack-,lem _ _ _ r
... | x1 ,, x2 ,, refl ,, z0 ,, z1
  with cek2ckFrame--·⋆lem x2 z1
... | refl with thm65bV (dischargeB-lem' {b = b}{x = app⋆ x₁ refl refl}) dischargeB-lem'' z0 x
... | V' ,, x' ,, y1 ,, y2 = V' ,, step* refl x' ,, y1 ,, y2
thm65bV {s = s CK., Red.wrap- } {W = W} {s' = s'} refl q r (CK.step* refl x)
  with cek2ckStack-,lem _ _ _ r
... | s' ,, f' ,, refl ,, x2 ,, x3
  with cek2ckFrame-wrap-lem _ x3
... | refl with thm65bV refl (cong Red.V-wrap q) x2 x
... | _  ,, x' ,, _ ,, y1 = _ ,, step* refl x' ,, _ ,, y1
thm65bV {s = s CK., Red.unwrap- } {W = W} {s' = s'} p q r (CK.step* refl x)
  with cek2ckStack-,lem _ _ _ r
thm65bV {M = wrap _ _ M} {.(cek2ckStack s') CK., Red.unwrap- } {W = Red.V-wrap W} {W' = V-wrap W'} refl refl r (CK.step* refl x) | s' ,, f' ,, refl ,, refl ,, x3
  with thm65bV refl refl refl (fast-forward (cek2ckStack s') (CK.□ _) (Red.deval (cek2ckVal W')) (cek2ckVal W') x)
... | _ ,, x' ,, _ ,, y1
  with cek2ckFrame-unwrap-lem _ x3
thm65bV {L = _} {.(wrap _ _ _)} {.(cek2ckStack s') CK., Red.unwrap- } {_} {Red.V-wrap W} {V-wrap W'} {.(s' , unwrap-)} p q r (CK.step* refl x) | s' ,, .unwrap- ,, refl ,, refl ,, x1 | _ ,, x' ,, _ ,, y1 | refl = _ ,, step* refl x' ,, _ ,, y1
-- -}
