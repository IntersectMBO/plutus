{-# OPTIONS -Wall #-}







module Elaboration.Contexts where

import Utils.Env
import Utils.Names
import Utils.Vars
import PlutusTypes.ConSig
import PlutusTypes.Type
import qualified PlutusCore.Term as Core







-- | A signature is a collection of type constructors, and data constructors
-- together with their constructor signatures. This is used during type
-- checking and elaboration to define the underlying type theory. We reuse
-- constructor signatures for the signatures of built-in functions as they're
-- formally equivalent.

data Signature
  = Signature
    { typeConstructors :: [(String,TyConSig)]
    , dataConstructors :: [(String,ConSig)]
    }





-- | A definition consists of a declared name together with its definition
-- and its type.

type Definitions = [(Sourced String,(Core.Term,Type))]

definitionsToEnvironment :: Definitions -> Env (Sourced String) Core.Term
definitionsToEnvironment defs =
  [ (x,m) | (x,(m,_)) <- defs ]





-- | A context contains generated variables together with their types.

type Context = [(FreeVar,Type)]





-- | A type variable context contains the names of free type variables.

type TyVarContext = [(FreeVar,())]

tyVarContextFromFreeVars :: [FreeVar] -> TyVarContext
tyVarContextFromFreeVars = map (\x -> (x,()))





-- | A @HypContext@ is the collection of hypothetical contexts, consisting of
-- a type variable context and a variable context.

data HypContext
  = HypContext
    { tyVarContext :: TyVarContext
    , context :: Context
    }

emptyHypContext :: HypContext
emptyHypContext = HypContext [] []





-- | A @DeclContext@ is the collection of declaration information, consisting
-- of a signature and some definitioins.

data DeclContext
  = DeclContext
    { signature :: Signature
    , definitions :: Definitions
    }

emptyDeclContext :: DeclContext
emptyDeclContext =
  DeclContext
    { signature = Signature
        { typeConstructors = []
        , dataConstructors = []
        }
    , definitions = []
    }