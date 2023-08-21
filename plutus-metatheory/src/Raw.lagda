\begin{code}
module Raw where
\end{code}

\begin{code}
open import Data.String using (String;_++_)
open import Data.Nat using (ℕ;_≟_)
open import Data.Integer using (ℤ)
open import Data.Integer.Show using (show)
open import Data.Unit using (⊤)
open import Relation.Nullary using (Reflects;Dec;ofʸ;ofⁿ;_because_;yes;no;does)
open import Relation.Binary.PropositionalEquality using (_≡_;cong;cong₂;refl)
open import Data.Bool using (Bool;false;true;_∧_)

open import Builtin using (Builtin;equals;decBuiltin)
open Builtin.Builtin

open import Builtin.Constant.AtomicType using (AtomicTyCon;decAtomicTyCon)
open AtomicTyCon

open import Utils using (Kind;*;♯;_⇒_;List;[];_∷_)
open import RawU using (TagCon;tagCon;Tag;decTagCon)
open Tag
\end{code}

The raw un-scope-checked and un-type-checked syntax

\begin{code}
data RawTy : Set

data RawTyCon : Set

data RawTy where
  `   : ℕ → RawTy
  _⇒_ : RawTy → RawTy → RawTy
  Π   : Kind → RawTy → RawTy
  ƛ   : Kind → RawTy → RawTy
  _·_ : RawTy → RawTy → RawTy
  con : RawTyCon → RawTy
  μ   : RawTy → RawTy → RawTy
  SOP : (tss : List (List RawTy)) → RawTy

{-# COMPILE GHC RawTy = data RType (RTyVar | RTyFun | RTyPi | RTyLambda | RTyApp | RTyCon | RTyMu | RTySOP) #-}

{-# FOREIGN GHC import Raw #-}

data RawTyCon where
  atomic     : AtomicTyCon → RawTyCon
  list       : RawTyCon
  pair       : RawTyCon

{-# COMPILE GHC RawTyCon = data RTyCon (RTyConAtom | RTyConList | RTyConPair) #-}

data RawTm : Set where
  `             : ℕ → RawTm
  Λ             : Kind → RawTm → RawTm
  _·⋆_          : RawTm → RawTy → RawTm
  ƛ             : RawTy → RawTm → RawTm
  _·_           : RawTm → RawTm → RawTm
  con           : TagCon → RawTm
  error         : RawTy → RawTm
  builtin       : Builtin → RawTm
  wrap          : RawTy → RawTy → RawTm → RawTm
  unwrap        : RawTm → RawTm
  constr        : (A : RawTy) → (i : ℕ) → (cs : List RawTm) → RawTm
  case          : (A : RawTy) → (arg : RawTm) → (cs : List RawTm) → RawTm

{-# COMPILE GHC RawTm = data RTerm (RVar | RTLambda  | RTApp | RLambda  | RApp | RCon | RError | RBuiltin | RWrap | RUnWrap | RConstr | RCase) #-}

-- α equivalence

-- we don't have a decidable equality instance for bytestring, so I
-- converted this to bool for now

decRTyCon : (C C' : RawTyCon) → Bool
decRTyCon (atomic t) (atomic t')  = does (decAtomicTyCon t t')
decRTyCon pair       pair         = true
decRTyCon list       list         = true
decRTyCon _          _            = false

decRKi : (K K' : Kind) → Bool
decRKi * * = true
decRKi * _ = false
decRKi ♯ ♯ = true
decRKi ♯ _ = false
decRKi (K ⇒ J) (K' ⇒ J') = decRKi K K' ∧ decRKi J J' 
decRKi (K ⇒ J) _ = false

decRTy : (A A' : RawTy) → Bool
decRTyList : (A A' : List RawTy) → Bool
decRTyListList : (A A' : List (List RawTy)) → Bool

decRTy (` x) (` x') = does (x ≟ x')
decRTy (A ⇒ B) (A' ⇒ B')    = decRTy A A' ∧ decRTy B B'
decRTy (Π K A) (Π K' A')    = decRKi K K' ∧ decRTy A A'
decRTy (ƛ K A) (ƛ K' A')    = decRKi K K' ∧ decRTy A A'
decRTy (A · B) (A' · B')    = decRTy A A' ∧ decRTy B B'
decRTy (con c) (con c')     = decRTyCon c c'
decRTy (μ A B) (μ A' B')    = decRTy A A' ∧ decRTy B B'
decRTy (SOP tss) (SOP tss') = decRTyListList tss tss'
decRTy _ _ = false

decRTyList [] [] = true
decRTyList (x ∷ xs) (x' ∷ xs') = decRTy x x' ∧ decRTyList xs xs'
decRTyList _ _ = false

decRTyListList [] [] = true
decRTyListList (xs ∷ xss) (xs' ∷ xss') = decRTyList xs xs' ∧ decRTyListList xss xss'
decRTyListList _ _ = false


decRTm : (t t' : RawTm) → Bool
decRTmList  : (t t' : List RawTm) → Bool

decRTm (` x) (` x')                       = does (x ≟ x')
decRTm (Λ K t) (Λ K' t')                  = decRKi K K' ∧ decRTm t t'
decRTm (t ·⋆ A) (t' ·⋆ A')                = decRTm t t' ∧ decRTy A A'
decRTm (ƛ A t) (ƛ A' t')                  = decRTy A A' ∧ decRTm t t'
decRTm (t · u) (t' · u')                  = decRTm t t' ∧ decRTm u u'
decRTm (con c) (con c')                   = decTagCon c c'
decRTm (error A) (error A')               = decRTy A A'
decRTm (builtin b) (builtin b')           = does (decBuiltin b b')
decRTm (wrap pat ar t) (wrap pat' ar' t') = decRTy pat pat' ∧ decRTy ar ar' ∧ decRTm t t'
decRTm (unwrap t) (unwrap t')             = decRTm t t'
decRTm (constr A i cs) (constr A' i' cs') = decRTy A A' ∧ does (i ≟ i') ∧ decRTmList cs cs'
decRTm (case A arg cs) (case A' arg' cs') = decRTy A A' ∧ decRTm arg arg' ∧ decRTmList cs cs'
decRTm _ _ = false

decRTmList [] [] = true
decRTmList (x ∷ t) (x' ∷ t') = decRTm x x' ∧ decRTmList t t'
decRTmList _ _ = false

-- We have to different approaches to de Bruijn terms.
-- one counts type and term binders separately the other counts them together

addBrackets : String → String 
addBrackets xs = "[" ++ xs ++ "]"

rawTyPrinter : RawTy → String
rawTyListPrinter : List (RawTy) → String
rawTyListListPrinter : List (List (RawTy)) → String

rawTyPrinter (` x)     = show (ℤ.pos x)
rawTyPrinter (A ⇒ B)   = "(" ++ rawTyPrinter A ++ "⇒" ++ rawTyPrinter B ++ ")"
rawTyPrinter (Π K A)   = "(Π" ++ "kind" ++ rawTyPrinter A ++ ")"
rawTyPrinter (ƛ K A)   = "(ƛ" ++ "kind" ++ rawTyPrinter A ++ ")"
rawTyPrinter (A · B)   = "(" ++ rawTyPrinter A ++ "·" ++ rawTyPrinter B ++ ")"
rawTyPrinter (con c)   = "(con)"
rawTyPrinter (μ A B)   = "(μ" ++ rawTyPrinter A ++ rawTyPrinter B ++ ")"
rawTyPrinter (SOP xss) =  addBrackets (rawTyListListPrinter xss)

rawTyListPrinter [] = ""
rawTyListPrinter (x ∷ []) = rawTyPrinter x
rawTyListPrinter (x ∷ y ∷ xs) = rawTyPrinter x ++ " , " ++ rawTyListPrinter (y ∷ xs)

rawTyListListPrinter [] = ""
rawTyListListPrinter (xs ∷ []) = addBrackets (rawTyListPrinter xs)
rawTyListListPrinter (xs ∷ ys ∷ xss) = addBrackets (rawTyListPrinter xs) ++ " , " ++ rawTyListListPrinter (ys ∷ xss)

rawListPrinter : List RawTm → String
rawPrinter : RawTm → String
rawPrinter (` x) = show (ℤ.pos x)
rawPrinter (Λ K t) = "(" ++ "Λ" ++ "kind" ++ rawPrinter t ++ ")"
rawPrinter (t ·⋆ A) = "(" ++ rawPrinter t ++ "·⋆" ++ rawTyPrinter A ++ ")"
rawPrinter (ƛ A t) = "(" ++ "ƛ" ++ rawTyPrinter A ++ rawPrinter t ++ ")"
rawPrinter (t · u) = "(" ++ rawPrinter t ++ "·" ++ rawPrinter u ++ ")"
rawPrinter (con c) = "(con)"
rawPrinter (error A) = "(error" ++ rawTyPrinter A ++ ")"
rawPrinter (builtin b) = "(builtin)"
rawPrinter (wrap pat ar t) = "(wrap" ++ ")"
rawPrinter (unwrap t) = "(unwrap" ++ rawPrinter t ++ ")"
rawPrinter (constr A i cs) = "(const"  ++ rawTyPrinter A 
                               ++ " "  ++ show (ℤ.pos i) 
                               ++ " [" ++ rawListPrinter cs ++ "])"
rawPrinter (case A arg cs) = "(case"  ++ rawTyPrinter A 
                              ++ " "  ++ rawPrinter arg 
                              ++ " [" ++ rawListPrinter cs ++"])"                               

rawListPrinter [] = ""
rawListPrinter (x ∷ []) = rawPrinter x
rawListPrinter (x ∷ y ∷ xs) = rawPrinter x ++ " , " ++ rawListPrinter (y ∷ xs)                               
\end{code}
 