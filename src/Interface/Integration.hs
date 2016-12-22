{-# OPTIONS -Wall #-}







-- | This module defines the integration tools for Plutus.

module Interface.Integration where

import Utils.ABT
import Utils.Env
import Utils.Names
import Utils.Vars
import qualified PlutusCore.Evaluation as Core
import qualified PlutusCore.Term as Core
import qualified PlutusCore.Program as Core
import Plutus.Parser
import Elaboration.Elaboration
import Elaboration.Elaborator

import Data.List





-- | This function converts a program to a declaration environment.

programToDeclEnv :: Core.Program -> Env (Sourced String) Core.Term
programToDeclEnv (Core.Program _ _ decls) =
  [ (n,m) | Core.TermDeclaration n m _ <- decls ]

-- | This function parses and elaborates a program.

loadProgram :: String -> Either String Core.Program
loadProgram src =
  do prog <- parseProgram src
     (_, ElabState
         { _signature = Signature tyConSigs conSigs
         , _definitions = defs
         }) <- runElaborator0 (elabProgram prog)
     return $ Core.Program
              { Core.typeConstructors = tyConSigs
              , Core.constructors = conSigs
              , Core.termDeclarations =
                  [ Core.TermDeclaration m n ty
                  | (m,(n,ty)) <- defs
                  ]
              } --definitionsToEnvironment defs


-- | This function loads a validator program and ensures that it can be used
-- to validate a transaction.

loadValidator :: String -> Either String Core.Program
loadValidator src =
  do prog <- loadProgram src
     case Core.lookupDeclaration
            (User "validator")
            (Core.termDeclarations prog) of
       Nothing -> Left "Validators must declare the term `validator`"
       Just _ -> return prog


-- | This function loads a redeemer program and ensures that it can be used to
-- redeem a transaction.

loadRedeemer :: String -> Either String Core.Program
loadRedeemer src =
  do prog <- loadProgram src
     case Core.lookupDeclaration
            (User "redeemer")
            (Core.termDeclarations prog) of
       Nothing -> Left "Redeemers must declare the term `redeemer`"
       Just _ -> return prog


-- | This function takes validator and redeemer programs, ensures that they
-- are compatible by not having overlapping names, ensures that they can be
-- used to validate a transaction, and then combines them and returns them
-- together with the term that needs to be evaluated in order to validate the
-- transaction.

buildValidationScript
  :: Core.Program
  -> Core.Program
  -> Core.Program
  -> Either String (Core.Term, Env (Sourced String) Core.Term)
buildValidationScript stdlib valprog redprog =
  let stdlibenv = programToDeclEnv stdlib
      valenv = programToDeclEnv valprog
      redenv = programToDeclEnv redprog
      evalenv = stdlibenv ++ valenv ++ redenv
      declaredNames = map fst evalenv
      uniqNames = nub declaredNames
  in if length declaredNames == length uniqNames
     then
       case ( lookup (User "validator") valenv
            , lookup (User "redeemer") redenv
            ) of
         (Nothing,Nothing) ->
           Left $ "The validator script is missing `validator` and the "
               ++ "redeemer script is missing `redeemer`"
         (Nothing,Just _) ->
           Left "The validator script is missing `validator`"
         (Just _,Nothing) ->
           Left "The redeemer script is missing `redeemer`"
         (Just _,Just _) ->
           Right (validationScript, evalenv)
     else
       Left $ "The following names are declared more than once: "
           ++ unwords (map showSourced (nub (declaredNames \\ uniqNames)))
  where
    validationScript :: Core.Term
    validationScript =
      Core.bindH
        (Core.decnameH (User "redeemer"))
        "x"
        (Core.appH (Core.decnameH (User "validator"))
                   (Var (Free (FreeVar "x"))))

checkValidationResult
  :: (Core.Term, Env (Sourced String) Core.Term)
  -> Either String Bool
checkValidationResult (script, env) =
  do res <- Core.evaluate undefined {- !!! -} env 3750 script
     case res of
       In (Core.Success _) -> Right True
       In (Core.Failure _) -> Right False
       _                   -> Left $ "The validation result isn't of type "
                                  ++ "Comp (i.e. neither success nor failure)"
