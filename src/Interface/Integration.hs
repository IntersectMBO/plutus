{-# OPTIONS -Wall #-}







-- | This module defines the integration tools for Plutus.

module Interface.Integration where

import Utils.ABT
--import Utils.Elaborator
import Utils.Env
import Utils.Names
import qualified Utils.ProofDeveloper as PD
import Utils.Vars
--import qualified Plutus.Program as Plutus
import qualified PlutusCore.Evaluation as Core
import qualified PlutusCore.Term as Core
import qualified PlutusCore.Program as Core
import Plutus.Parser
import Elaboration.Contexts
import Elaboration.Elaboration ()
import Elaboration.Elaborator
import Elaboration.Judgments

import Control.Monad.Except
import Data.List
import qualified Data.ByteString.Lazy as BS





-- | This function converts a program to a declaration environment.

programToDeclEnv :: Core.Program -> Env (Sourced String) Core.Term
programToDeclEnv (Core.Program _ _ defs) = definitionsToEnvironment defs



-- | This function parses and elaborates a program.

loadProgram :: DeclContext
            -> String
            -> Either String Core.Program --Elaborator Core.Program
loadProgram dctx src =
  case parseProgram src of
    Left err -> Left err
    Right p ->
      case runElaborator (PD.elaborator (ElabProgram dctx p)) of
        Left elabErr ->
          Left (PD.showElabError elabErr)
        Right (dctx', _) ->
          Right
            (Core.Program
              { Core.typeConstructors =
                  typeConstructors (signature dctx')
              , Core.constructors =
                  dataConstructors (signature dctx')
              , Core.termDeclarations =
                  definitions dctx'
              })




-- | This function loads a validator program and ensures that it can be used
-- to validate a transaction.

loadValidator :: DeclContext -> String -> Either String Core.Program
loadValidator dctx src =
  do prog <- loadProgram dctx src
     case lookup (User "validator") (Core.termDeclarations prog) of
       Nothing -> throwError "Validators must declare the term `validator`"
       Just _ -> return prog




-- | This function loads a redeemer program and ensures that it can be used to
-- redeem a transaction.

loadRedeemer :: DeclContext -> String -> Either String Core.Program
loadRedeemer dctx src =
  do prog <- loadProgram dctx src
     case lookup (User "redeemer") (Core.termDeclarations prog) of
       Nothing -> throwError "Redeemers must declare the term `redeemer`"
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
buildValidationScript
  (Core.Program stdlibTyCons stdlibCons stdlibDefs)
  (Core.Program valTyCons valCons valDefs)
  (Core.Program redTyCons redCons redDefs)
  =
  let evalTyCons = stdlibTyCons ++ valTyCons ++ redTyCons
      evalCons = stdlibCons ++ valCons ++ redCons
      evalDefs = stdlibDefs ++ valDefs ++ redDefs
  in
    case ( repeats (map fst evalTyCons)
         , repeats (map fst evalCons)
         , repeats (map fst evalDefs)
         ) of
      ([],[],[]) ->
        case ( lookup (User "validator") valDefs
             , lookup (User "redeemer") redDefs
             ) of
         (Nothing,Nothing) ->
           throwError
             $ "The validator script is missing `validator` and the "
               ++ "redeemer script is missing `redeemer`"
         (Nothing,Just _) ->
           throwError "The validator script is missing `validator`"
         (Just _,Nothing) ->
           throwError "The redeemer script is missing `redeemer`"
         (Just _,Just _) ->
           return (validationScript, definitionsToEnvironment evalDefs)
      ([],[],xs) ->
        throwError
          $ "There are overlapping declared names in these scripts: "
            ++ unwords (map show xs)
      ([],xs,_) ->
        throwError
          $ "There are overlapping constructors in these scripts: "
            ++ unwords (map show xs)
      (xs,_,_) ->
        throwError
          $ "There are overlapping type constructors in these scripts: "
            ++ unwords (map show xs)
  where
    repeats :: Eq a => [a] -> [a]
    repeats xs = xs \\ nub xs
    
    validationScript :: Core.Term
    validationScript =
      Core.bindH
        (Core.decnameH (User "redeemer") [])
        "x"
        (Core.appH (Core.decnameH (User "validator") [])
                   (Var (Free (FreeVar "x"))))



checkValidationResult
  :: BS.ByteString
  -> (Core.Term, Env (Sourced String) Core.Term)
  -> Either String Bool
checkValidationResult txInfo (script, env) =
  do res <- Core.evaluate (Core.TransactionInfo txInfo) env 3750 script
     case res of
       In (Core.Success _) -> Right True
       In (Core.Failure _) -> Right False
       _                   -> Left $ "The validation result isn't of type "
                                  ++ "Comp (i.e. neither success nor failure)"