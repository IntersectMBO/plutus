{-# OPTIONS -Wall #-}







-- | This module defines the integration tools for Plutus.

module Interface.Integration where

import Utils.ABT
import Utils.Elaborator
import Utils.Env
import Utils.Names
import Utils.Vars
import qualified Plutus.Program as Plutus
import qualified PlutusCore.Evaluation as Core
import qualified PlutusCore.Term as Core
import qualified PlutusCore.Program as Core
import Plutus.Parser
import Elaboration.Elaboration
import Elaboration.Elaborator

import Control.Monad.Except
import Data.List





-- | This function converts a program to a declaration environment.

programToDeclEnv :: Core.Program -> Env (Sourced String) Core.Term
programToDeclEnv (Core.Program _ _ defs) = definitionsToEnvironment defs



-- | This function parses and elaborates a program.

loadProgram :: String -> Elaborator Core.Program
loadProgram src =
  case parseProgram src of
    Left err -> throwError err
    Right (Plutus.Program stmts) ->
      do oldDefs <- getElab definitions
         Signature oldTypeCons oldCons <- getElab signature
         mapM_ elabStatement stmts
         newDefs <- getElab definitions
         Signature newTypeCons newCons <- getElab signature
         let deltaTypeCons =
               deleteFirstsBy
                 (\x y -> fst x == fst y)
                 newTypeCons
                 oldTypeCons
             deltaCons =
               deleteFirstsBy
                 (\x y -> fst x == fst y)
                 newCons
                 oldCons
             deltaDefs =
               deleteFirstsBy
                 (\x y -> fst x == fst y)
                 newDefs
                 oldDefs
         return $ Core.Program
                    deltaTypeCons
                    deltaCons
                    deltaDefs



-- | This function loads a validator program and ensures that it can be used
-- to validate a transaction.

loadValidator :: String -> Elaborator Core.Program
loadValidator src =
  do prog <- loadProgram src
     defs <- getElab definitions
     case lookup (User "validator") defs of
       Nothing -> throwError "Validators must declare the term `validator`"
       Just _ -> return prog



-- | This function loads a redeemer program and ensures that it can be used to
-- redeem a transaction.

loadRedeemer :: String -> Elaborator Core.Program
loadRedeemer src =
  do prog <- loadProgram src
     defs <- getElab definitions
     case lookup (User "redeemer") defs of
       Nothing -> throwError "Redeemers must declare the term `redeemer`"
       Just _ -> return prog



-- | We can run an elaborator in the context of some previous program, e.g.
-- a standard library.

runElabInContext :: Core.Program -> Elaborator a -> Either String a
runElabInContext (Core.Program tyConSigs conSigs defs) m =
  fmap fst (runElaborator m (Signature tyConSigs conSigs) defs [])



-- | We can elab in an empty context as well.

runElabNoContext :: Elaborator a -> Either String a
runElabNoContext m = fmap fst (runElaborator0 m)



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