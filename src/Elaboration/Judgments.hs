{-# OPTIONS -Wall #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}







module Elaboration.Judgments where

import Utils.ABT
import qualified Utils.ProofDeveloper as PD
--import Utils.Vars
import Elaboration.Contexts
import Elaboration.ElabState
import PlutusTypes.ConSig
import PlutusTypes.Type
import Plutus.Program
import Plutus.Term
import qualified PlutusCore.Term as Core







data Judgment r where
  -- DECL ⊢ stmt ; stmts ⊣ DECL
  ElabProgram :: DeclContext
              -> Program
              -> Judgment DeclContext
  
  -- DECL ⊢ term n type A def M ⊣ DECL
  ElabTermDecl :: DeclContext
               -> TermDeclaration
               -> Judgment DeclContext
  
  -- DECL ⊢ c A* alt n α* ⊣ DECL
  ElabAlt :: DeclContext
          -> String
          -> ConSig
          -> Judgment DeclContext
  
  -- DECL ⊢ type n α* alts C0 | ... | Cj ⊣ DECL
  ElabTypeDecl :: DeclContext
               -> TypeDeclaration
               -> Judgment DeclContext
  
  {-
  -- CTX ⊢ D ∋ a
  TyVarExists :: HypContext
              -> FreeVar
              -> Judgment ()
  
  -- DECL ⊢ c tycon
  TyConExists :: DeclContext
              -> String
              -> Judgment TyConSig
  
  TypeInContext :: HypContext
                -> FreeVar 
                -> Judgment Type
  -}
  
  -- DECL ; CTX ⊢ A type
  IsType :: DeclContext
         -> HypContext
         -> Type
         -> Judgment ()
  
  -- DECL ; CTX ⊢ M ▹ M' ∈ A ⊣ DECL
  Synth :: DeclContext
        -> HypContext
        -> Term
        -> Judgment (Core.Term, Type, DeclContext)
  
  -- DECL ; CTX ⊢ P* → M ▹ P'* → M' from A* to B ⊣ DECL
  SynthClause :: DeclContext
              -> HypContext
              -> [Type]
              -> Clause
              -> Judgment (Core.Clause, Type, DeclContext)
  
  -- DECL ; CTX ⊢ A ∋ M ▹ M' ⊣ DECL
  Check :: DeclContext
        -> HypContext
        -> Type
        -> Term
        -> Judgment (Core.Term, DeclContext)
  
  -- DECL ; CTX ⊢ A pattern P ▹ P'
  CheckPattern :: DeclContext
               -> Type
               -> Pattern
               -> Judgment (Core.Pattern, [Type])
  
  -- DECL ⊢ [α*](A0,...,An)B consig
  CheckConSig :: DeclContext
              -> ConSig
              -> Judgment ()
  
  -- A =!= B
  Unify :: Type -> Type -> Judgment ()
  
  UnifyAll :: [Type] -> Judgment Type
  
  -- A ⊑ B
  Subtype :: HypContext -> Type -> Type -> Judgment ()






substituteHypContext :: ElabState -> HypContext -> HypContext
substituteHypContext s hctx =
  hctx
    { context =
        [ (x,substMetas (substitution s) t)
          | (x,t) <- context hctx
          ]
    }
  

instance PD.Metas ElabState Judgment where
  substitute s (ElabProgram dctx prog) =
    ElabProgram
      dctx
      (substTypeMetasProgram (substitution s) prog)
  substitute s (ElabTermDecl dctx tmdecl) =
    ElabTermDecl
      dctx
      (substTypeMetasTermDecl (substitution s) tmdecl)
  substitute s (ElabAlt dctx c consig) =
    ElabAlt
      dctx
      c
      (substMetasConSig (substitution s) consig)
  substitute s (ElabTypeDecl dctx tydecl) =
    ElabTypeDecl
      dctx
      (substTypeMetasTypeDecl (substitution s) tydecl)
  {-
  substitute s (TyVarExists hctx x) =
    TyVarExists (substituteHypContext s hctx) x
  substitute _ (TyConExists dctx c) =
    TyConExists dctx c
  substitute s (TypeInContext hctx x) =
    TypeInContext (substituteHypContext s hctx) x
  -}
  substitute s (IsType dctx hctx a) =
    IsType
      dctx
      (substituteHypContext s hctx)
      (substMetas (substitution s) a)
  substitute s (Synth dctx hctx m) =
    Synth
      dctx
      (substituteHypContext s hctx)
      (substTypeMetas (substitution s) m)
  substitute s (SynthClause dctx hctx as cl) =
    SynthClause
      dctx
      (substituteHypContext s hctx)
      (map (substMetas (substitution s)) as)
      (substTypeMetasClause (substitution s) cl)
  substitute s (Check dctx hctx a m) =
    Check
      dctx
      (substituteHypContext s hctx)
      (substMetas (substitution s) a)
      (substTypeMetas (substitution s) m)
  substitute s (CheckPattern dctx a pat) =
    CheckPattern
      dctx
      (substMetas (substitution s) a)
      pat
  substitute s (CheckConSig dctx consig) =
    CheckConSig
      dctx
      (substMetasConSig (substitution s) consig)
  substitute s (Unify a b) =
    Unify
      (substMetas (substitution s) a)
      (substMetas (substitution s) b)
  substitute s (UnifyAll as) =
    UnifyAll (map (substMetas (substitution s)) as)
  substitute s (Subtype hctx a b) =
    Subtype
      (substituteHypContext s hctx)
      (substMetas (substitution s) a)
      (substMetas (substitution s) b)