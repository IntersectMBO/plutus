{-# OPTIONS -Wall #-}







module Elaboration.ElabState where

import Utils.Unifier
import Utils.Vars
import PlutusTypes.Type







-- | The definition of the state to be carried by the type checking monad for
-- this particular variant. We need only the bare minimum of a signature,
-- some defined terms, and a typing context.

data ElabState
  = ElabState
    { substitution :: Substitution TypeF
    , nextMeta :: MetaVar
    , nextGeneratedNameIndex :: Int
    , currentNameBeingDeclared :: String
    }

initialElabState :: ElabState
initialElabState =
  ElabState [] (MetaVar 0) 0 ""