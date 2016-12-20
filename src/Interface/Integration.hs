{-# OPTIONS -Wall #-}







-- | This module defines the integration tools for Plutus.

module Interface.Integration where

import Utils.ABT
import Utils.Env
import Utils.Names
import Utils.Vars
import qualified PlutusCore.Term as Core
import qualified PlutusCore.Program as Core
import Plutus.Parser
import Elaboration.Elaboration
import Elaboration.Elaborator





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
  -> Either String (Core.Term, Env (Sourced String) Core.Term)
buildValidationScript valprog redprog =
  let valenv = programToDeclEnv valprog
      redenv = programToDeclEnv redprog
  in case [ n | (n,_) <- valenv, any (\(n',_) -> n == n') redenv ] of
    [] ->
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
          Right (validationScript, valenv ++ redenv)
    ns ->
      Left $ "The following names are used in both validator and "
          ++ "redeemer scripts: " ++ unwords (map showSourced ns)
  where
    validationScript :: Core.Term
    validationScript =
      Core.bindH
        (Core.decnameH (User "redeemer"))
        "x"
        (Core.appH (Core.decnameH (User "validator"))
                   (Var (Free (FreeVar "x"))))