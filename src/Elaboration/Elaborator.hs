{-# OPTIONS -Wall #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}







-- This module defines the core types of a unification elaborator.

module Elaboration.Elaborator where

import Utils.ABT
--import Utils.Env
import Utils.Names
import Utils.Pretty
import qualified Utils.ProofDeveloper as PD
--import Utils.Unifier
import Utils.Vars
import Plutus.Program
import Plutus.Term
import PlutusTypes.ConSig
import PlutusTypes.Type
--import qualified PlutusCore.Term as Core
--import Elaboration.Contexts
import Elaboration.ElabState
import Elaboration.Judgments

--import qualified Control.Lens as L
import Control.Monad.State












newtype ElabError = ElabError String

type Decomposer = PD.Decomposer ElabState ElabError Judgment

type Elaborator = PD.Elaborator ElabState ElabError Judgment

type TypeChecker = Elaborator

runElaborator :: Elaborator a
              -> Either (PD.ElabError ElabState ElabError Judgment)
                        (a,ElabState)
runElaborator e =
  PD.runElaborator e [] (ElabState [] (MetaVar 0) 0 "")




newMeta :: Decomposer MetaVar
newMeta =
  do s <- get
     put (s { nextMeta = nextMeta s + 1 })
     return (nextMeta s)

assignMeta :: MetaVar -> Type -> Decomposer ()
assignMeta x a =
  do s <- get
     put (s { substitution = (x,a) : substitution s })

newGeneratedNameIndex :: Decomposer Int
newGeneratedNameIndex =
  do s <- get
     put (s { nextGeneratedNameIndex = nextGeneratedNameIndex s + 1 })
     return (nextGeneratedNameIndex s)

nameBeingDeclared :: Decomposer String
nameBeingDeclared =
  do s <- get
     return (currentNameBeingDeclared s)




instance PD.ShowElabError ElabState ElabError Judgment where
  showElabError (PD.ElabError (ElabError err) _ ctx (PD.Any g0)) =
     "Could not prove " ++ prettyJudgment g0
      ++ "\nError message: " ++ err
      -- ++ "\nElaboration state: " ++ prettyElabState s
      ++ "\nContext:" ++ go ctx
    where
      go :: PD.Context (PD.Any Judgment) -> String
      go [] = ""
      go ((_,PD.Any (ElabProgram _ _)):gs) =
        go gs
      go ((i,PD.Any g):gs) =
        "\n\n  Which is subproblem " ++ show i ++ " of "
          ++ prettyJudgment g ++ go gs
      
      prettyJudgment :: Judgment r -> String
      prettyJudgment (ElabProgram _ _) =
        "<program>"
      prettyJudgment (ElabTermDecl _ tmdecl) =
        "the declaration for `"
        ++ showSourced (termDeclarationName tmdecl)
        ++ "`"
      prettyJudgment (ElabAlt _ n (ConSig ascs _)) =
        "the constructor alternative "
        ++ "`" ++ n ++ " "
        ++ unwords (map (parenthesize (Just TyConArg) . body) ascs)
        ++ "`"
      prettyJudgment (ElabTypeDecl _ (TypeDeclaration tycon args _)) =
        "the type declaration for `" ++ tycon ++ " " ++ unwords args ++ "`"
      prettyJudgment (IsType _ _ a) =
        "checking that `" ++ pretty a ++ "` is a type"
      prettyJudgment (IsPolymorphicType _ _ a) =
        "checking that `" ++ pretty a ++ "` is a polymorphic type"
      prettyJudgment (Synth _ _ m) =
        "synthesizing the type of `" ++ pretty m ++ "`"
      prettyJudgment (SynthClause _ _ _ (Clause pscs bsc)) =
        "synthesizing the type of the clause `"
        ++ unwords (map (parenthesize (Just ConPatArg) . body) pscs)
        ++ " -> "
        ++ pretty (body bsc)
        ++ "`"
      prettyJudgment (Check _ _ a m) =
        "checking that the type `" ++ pretty a
        ++ "` contains the program `" ++ pretty m ++ "`"
      prettyJudgment (CheckPattern _ a pat) =
        "checking that the type `" ++ pretty a
        ++ "` contains the pattern `" ++ pretty pat ++ "`"
      prettyJudgment (CheckConSig _ consig) =
        "checking the validity of the constructor signature `"
        ++ show consig
        ++ "`"
      prettyJudgment (Unify a b) =
        "unifying `" ++ pretty a ++ "` and `" ++ pretty b ++ "`"
      prettyJudgment (UnifyAll as) =
        "unifying the types "
        ++ unwords (map (\a -> "`" ++ pretty a ++ "`") as)
      prettyJudgment (Subtype a b) =
        "checking that `" ++ pretty a
        ++ "` is a subtype of `" ++ pretty b ++ "`"