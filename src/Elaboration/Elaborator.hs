{-# OPTIONS -Wall #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}







-- This module defines the core types of a unification elaborator.

module Elaboration.Elaborator where

import Utils.Env
import Utils.Unifier
import Utils.Vars
import Plutus.ConSig
import Plutus.Type
import qualified PlutusCore.Term as Core

import qualified Control.Lens as L
import Control.Monad.State







-- | A type constructor's signature consists of just the number of parameters
-- the constructor has.

newtype TyConSig = TyConSig Int





-- | A signature is a collection of type constructors, and data constructors
-- together with their constructor signatures. This is used during type
-- checking and elaboration to define the underlying type theory. We reuse
-- constructor signatures for the signatures of built-in functions as they're
-- formally equivalent.

data Signature
  = Signature
    { _typeConstructors :: [(String,TyConSig)]
    , _dataConstructors :: [(String,ConSig)]
    , _builtins :: [(String,ConSig)]
    }
L.makeLenses ''Signature





-- | A definition consists of a declared name together with its definition
-- and its type.

type Definitions = [(String,(Core.Term,Type))]

definitionsToEnvironment :: Definitions -> Env String Core.Term
definitionsToEnvironment defs =
  [ (x,m) | (x,(m,_)) <- defs ]





-- | A context contains generated variables together with their types.

type Context = [(FreeVar,Type)]





-- | A type variable context contains the names of free type variables.

type TyVarContext = [FreeVar]





-- | The definition of the state to be carried by the type checking monad for
-- this particular variant. We need only the bare minimum of a signature,
-- some defined terms, and a typing context.

data ElabState
  = ElabState
    { _signature :: Signature
    , _definitions :: Definitions
    , _context :: Context
    , _tyVarContext :: TyVarContext
    , _substitution :: Substitution TypeF
    , _nextMeta :: MetaVar
    }
L.makeLenses ''ElabState


type Elaborator = StateT ElabState (Either String)


type TypeChecker = Elaborator


runElaborator :: Elaborator a
              -> Signature
              -> Definitions
              -> Context
              -> Either String (a,ElabState)
runElaborator e sig defs ctx =
  runStateT e (ElabState sig defs ctx [] [] (MetaVar 0))


runElaborator0 :: Elaborator a -> Either String (a,ElabState)
runElaborator0 e = runElaborator e (Signature [] [] []) [] []


when' :: Elaborator a -> Elaborator () -> Elaborator ()
when' e1 e2 = do s <- get
                 case runStateT e1 s of
                   Left _ -> return ()
                   Right _  -> e2