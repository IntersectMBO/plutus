{-# OPTIONS -Wall #-}







-- | This module defines the integration tools for Plutus.

module Elaboration.Integration where

import Utils.ABT
import Utils.Env
import Utils.Vars
import qualified PlutusCore.Term as Core
import Plutus.Parser
import Elaboration.Elaboration
import Elaboration.Elaborator





-- | This function parses and elaborates a program.

loadProgram :: String -> Either String (Env String Core.Term)
loadProgram src =
  do prog <- parseProgram src
     (_,ElabState _ defs _ _ _ _) <- runElaborator0 (elabProgram prog)
     return $ definitionsToEnvironment defs


-- | This function loads a validator program and ensures that it can be used
-- to validate a transaction.

loadValidator :: String -> Either String (Env String Core.Term)
loadValidator src =
  do env <- loadProgram src
     case lookup "validator" env of
       Nothing -> Left "Validators must declare the term `validator`"
       Just _ -> return env


-- | This function loads a redeemer program and ensures that it can be used to
-- redeem a transaction.

loadRedeemer :: String -> Either String (Env String Core.Term)
loadRedeemer src =
  do env <- loadProgram src
     case lookup "redeemer" env of
       Nothing -> Left "Redeemers must declare the term `redeemer`"
       Just _ -> return env


-- | This function takes validator and redeemer programs, ensures that they
-- are compatible by not having overlapping names, ensures that they can be
-- used to validate a transaction, and then combines them and returns them
-- together with the term that needs to be evaluated in order to validate the
-- transaction.

buildValidationScript
  :: Env String Core.Term
  -> Env String Core.Term
  -> Either String (Core.Term, Env String Core.Term)
buildValidationScript valenv redenv =
  case [ n | (n,_) <- valenv, any (\(n',_) -> n == n') redenv ] of
    [] ->
      case (lookup "validator" valenv, lookup "redeemer" redenv) of
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
          ++ "redeemer scripts: " ++ unwords ns
  where
    validationScript :: Core.Term
    validationScript =
      Core.bindH
        (Core.decnameH "redeemer")
        "x"
        (Core.appH (Core.decnameH "validator")
                   (Var (Free (FreeVar "x"))))