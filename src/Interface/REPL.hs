{-# OPTIONS -Wall #-}




module Interface.REPL where

import Utils.ABT
import Utils.Names
import Utils.Pretty
import qualified Utils.ProofDeveloper as PD
import qualified PlutusCore.Term as Core
import PlutusCore.Evaluation
import Plutus.Parser
import Plutus.Term
import Elaboration.Contexts
--import Elaboration.ElabState
import Elaboration.Elaboration ()
import Elaboration.Elaborator
import Elaboration.Judgments

import Data.Either.Combinators
import System.IO





flushStr :: String -> IO ()
flushStr str = putStr str >> hFlush stdout

readPrompt :: String -> IO String
readPrompt prompt = flushStr prompt >> getLine

until_ :: Monad m => (a -> Bool) -> m a -> (a -> m ()) -> m ()
until_ p prompt action = do 
   result <- prompt
   if p result 
      then return ()
      else action result >> until_ p prompt action

repl :: String -> IO ()
repl src0 = case loadProgram src0 of
             Left e -> flushStr ("ERROR: " ++ e ++ "\n")
             Right dctx --(sig,defs,ctx)
               -> do hSetBuffering stdin LineBuffering
                     until_ (== ":quit")
                            (readPrompt "$> ")
                            (evalAndPrint dctx)
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
         -- (_,ElabState sig defs ctx _ _ _ _ _) <- runElaborator0 (elabProgram prog)
         -- return (sig,defs,ctx)
    
    loadTerm :: DeclContext -> String -> Either String Core.Term
    loadTerm dctx src =
      do tm0 <- parseTerm src
         let tm = freeToDefined (In . Decname . User) tm0
         case runElaborator (PD.elaborator (Synth dctx emptyHypContext tm)) of
           Left e -> Left (PD.showElabError e)
           Right ((tm',_,dctx'),_) ->
             evaluate (TransactionInfo undefined {- !!! -})
                      (definitionsToEnvironment (definitions dctx'))
                      3750
                      tm' --runReaderT (eval tm') env
         {-
         case runElaborator (synth tm) sig defs ctx of
           Left e -> Left e
           Right ((tm',_),elabstate) ->
             evaluate (TransactionInfo undefined {- !!! -})
                      (definitionsToEnvironment (_definitions elabstate))
                      3750
                      tm' --runReaderT (eval tm') env
                      -}
                      
    evalAndPrint :: DeclContext -> String -> IO ()
    evalAndPrint _ "" = return ()
    evalAndPrint dctx ":defs" =
      flushStr
        (unlines
          [ showSourced n
            | (n,_) <- definitions dctx
            ]
          ++ "\n")
    evalAndPrint dctx src =
      case loadTerm dctx src of
        Left e -> flushStr ("ERROR: " ++ e ++ "\n")
        Right v -> flushStr (pretty v ++ "\n")

replFile :: String -> IO ()
replFile loc = readFile loc >>= repl