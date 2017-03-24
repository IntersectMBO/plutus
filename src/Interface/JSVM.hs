{-# OPTIONS -Wall #-}







module Interface.JSVM where

import Elaboration.Contexts
import Elaboration.Elaboration ()
import Elaboration.Elaborator
import Elaboration.Judgments
import Plutus.Term
import qualified PlutusCore.Term as Core
import Plutus.Parser
import Utils.ABT
import Utils.Env
import Utils.JSABT
import Utils.Names
import qualified Utils.ProofDeveloper as PD

import Data.Either.Combinators
import Data.List (intercalate)







environmentToJS :: Env (Sourced String) Core.Term -> String
environmentToJS env =
  "{ "
  ++ intercalate ", "
       [ "\"" ++ showSourced n ++ "\": " ++ jsABTToSource (toJS m)
       | (n,m) <- env
       ]
  ++ " }"

loadExpression :: String -> String -> Either String String
loadExpression decls expr =
  _
  where
    loadProgram
      :: String -> Either String DeclContext
    loadProgram src =
      do prog <- parseProgram src
         (dctx,_)
           <- mapLeft PD.showElabError
                      (runElaborator
                        (PD.elaborator
                          (ElabProgram emptyDeclContext prog)))
         return dctx
    
    parseAndElab :: DeclContext -> String -> Either String (Core.Term,DeclContext)
    parseAndElab dctx src =
      do tm0 <- parseTerm src
         let tm = freeToDefined (In . Decname . User) tm0
         case runElaborator (PD.elaborator (Synth dctx emptyHypContext tm)) of
           Left e -> Left (PD.showElabError e)
           Right ((tm',_,dctx'),_) -> Right (tm',dctx')