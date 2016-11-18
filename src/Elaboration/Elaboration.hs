{-# OPTIONS -Wall #-}







-- | This module defines how elaboration of programs is performed.

module Elaboration.Elaboration where

import Utils.ABT
import Utils.Elaborator
import Utils.Vars
import Plutus.ConSig
import Plutus.Term
import Plutus.Type
import Plutus.Program
import qualified PlutusCore.Term as Core
import qualified PlutusCore.Program as Core
import Elaboration.Elaborator
import Elaboration.TypeChecking

import Control.Monad.Except








-- | We can add a new defined value declaration given a name, core term,
-- and type.

addDeclaration :: String -> Core.Term -> Type -> Elaborator ()
addDeclaration n def ty = addElab definitions [(n,(def,ty))]


-- | We can add a new type constructor by giving a name and a type constructor
-- signature.

addTypeConstructor :: String -> TyConSig -> Elaborator ()
addTypeConstructor n sig = addElab (signature.typeConstructors) [(n,sig)]


-- | We can add a new data constructor by given a type constructor name, a
-- name for the data constructor, and a list of arg types from which to build
-- a constructor signature.

addConstructor :: String -> ConSig -> Elaborator ()
addConstructor n consig = addElab (signature.dataConstructors) [(n,consig)]





-- | Elaborating a term declaration takes one of two forms, depending on what
-- kind of declaration is being elaborated. A definition of the form
-- @f : A { M }@ is elaborated directly, while a definition of the form
-- @f : A { f x y z = M }@ is first transformed into the former
-- type of declaration, and then elaborated.
--
-- This corresponds to the elaboration judgment
-- @Σ;Δ ⊢ term n type A def M ⊣ Δ'@ which is defined as
--
-- @
--      Σ ⊢ A type   Σ ; Δ ; n : A ⊢ A ∋ M ▹ M'
--    -------------------------------------------
--    Σ ; Δ ⊢ term n type A def M ⊣ Δ, n : A ↦ M'
-- @

elabTermDecl :: TermDeclaration -> Elaborator ()
elabTermDecl (TermDeclaration n ty m) =
  do when' (typeInDefinitions n)
         $ throwError ("Term already defined: " ++ n)
     isType ty
     let def = freeToDefined (In . Decname) m
     def' <- extendElab definitions
               [(n,(error "This should never be used in elaboration.",ty))]
           $ check def ty
     addDeclaration n def' ty
elabTermDecl (WhereDeclaration n ty preclauses) =
  case preclauses of
    [] -> throwError "Cannot create an empty let-where definition."
    [(ps,xs,b)] | all isVarPat ps
      -> elabTermDecl
           (TermDeclaration
              n
              ty
              (helperFold lamH xs b))
    (ps0,_,_):_
      -> let clauses = [ clauseH xs ps b
                       | (ps,xs,b) <- preclauses
                       ]
             xs0 = [ "x" ++ show i | i <- [0..length ps0-1] ]
         in elabTermDecl
              (TermDeclaration
                 n
                 ty
                 (helperFold
                    lamH
                    xs0
                    (caseH (map (Var . Free . FreeVar) xs0) clauses)))
  where
    isVarPat :: Pattern -> Bool
    isVarPat (Var _) = True
    isVarPat _ = False





-- | Elaboration of a constructor in this variant is a relatively simple
-- process. This corresponds to the elaboration judgment
-- @Σ ⊢ c A* alt n α* ⊣ Σ'@ which is defined as
--
-- @
--                    Σ ; α* type ⊢ Ai type
--    -------------------------------------------------------
--    Σ ⊢ c A0 ... Ak alt n α* ⊣ Σ, c : [α*](A0,...,Ak)(n α*)
-- @
--
-- Because constructor signatures are a bundle in this implementation, we
-- define this in terms of the judgment @Γ ⊢ [α*](A0,...,An)B consig@ which
-- is implemented in the @checkifyConsig@ function.

elabAlt :: String -> ConSig -> Elaborator ()
elabAlt n consig =
  do when' (typeInSignature n)
         $ throwError ("Constructor already declared: " ++ n)
     checkifyConSig consig
     addConstructor n consig





-- | Elaboration of a type constructor is similar to elaborating a data
-- constructor, except it includes elaborations for the constructors as well.
--
-- @
--    Σ, n : *^k ⊢ C0 alt n α* ⊣ Σ'0
--    Σ'0 ⊢ C1 alt n α* ⊣ Σ'1
--    ...
--    Σ'j-1 ⊢ Cj alt n α* ⊣ Σ'j
--    --------------------------------------
--    Σ ⊢ type n α* alts C0 | ... | Cj ⊣ Σ'j
-- @
--
-- where here @Σ # c@ means that @c@ is not a type constructor in @Σ@.

elabTypeDecl :: TypeDeclaration -> Elaborator ()
elabTypeDecl (TypeDeclaration tycon params alts) =
  do when' (tyconExists tycon)
         $ throwError ("Type constructor already declared: " ++ tycon)
     addTypeConstructor tycon (TyConSig (length params))
     mapM_ (uncurry elabAlt) alts





-- Elaborating a whole program involves chaining together the elaborations of
-- each kind of declaration. We can define it inductively as follows:
--
-- @
--    -----------------
--    Σ ; Δ ⊢ ε ⊣ Σ ; Δ
--
--    Σ ⊢ type n α* alts C0 | ... Ck ⊣ Σ'   Σ' ; Δ ⊢ P ⊣ Σ'' ; Δ''
--    ------------------------------------------------------------
--        Σ ; Δ ⊢ data n α* = { C0 | ... | Ck} ; P ⊣ Σ'' ; Δ''
--
--    Σ ; Δ ⊢ term n type A def M ⊣ Δ'   Σ ; Δ' ⊢ P ⊣ Σ'' ; Δ''
--    ---------------------------------------------------------
--               Σ ; Δ ⊢ x : A { M } ; P ⊣ Σ'' ; Δ''
-- @

elabProgram :: Program -> Elaborator ()
elabProgram (Program stmts0) = go stmts0
  where
    go :: [Statement] -> Elaborator ()
    go [] = return ()
    go (TyDecl td:stmts) = do elabTypeDecl td
                              go stmts
    go (TmDecl td:stmts) = do elabTermDecl td
                              go stmts