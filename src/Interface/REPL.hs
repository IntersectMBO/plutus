{-# OPTIONS -Wall #-}




module Interface.REPL where

import Utils.ABT
import Utils.Names
import Utils.Pretty
import qualified PlutusCore.Term as Core
import PlutusCore.Evaluation
import Plutus.Parser
import Plutus.Term
import Elaboration.Elaboration
import Elaboration.Elaborator

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
             Right (sig,defs,ctx)
               -> do hSetBuffering stdin LineBuffering
                     until_ (== ":quit")
                            (readPrompt "$> ")
                            (evalAndPrint sig defs ctx)
  where
    loadProgram :: String -> Either String (Signature,Definitions,Context)
    loadProgram src =
      do prog <- parseProgram src
         (_,ElabState sig defs ctx _ _ _ _ _) <- runElaborator0 (elabProgram prog)
         return (sig,defs,ctx)
    
    loadTerm :: Signature -> Definitions -> Context -> String -> Either String Core.Term
    loadTerm sig defs ctx src =
      do tm0 <- parseTerm src
         let tm = freeToDefined (In . Decname . User) tm0
         case runElaborator (synth tm) sig defs ctx of
           Left e -> Left e
           Right ((tm',_),elabstate) ->
             evaluate (TransactionInfo undefined {- !!! -})
                      (definitionsToEnvironment (_definitions elabstate))
                      3750
                      tm' --runReaderT (eval tm') env
    
    evalAndPrint :: Signature -> Definitions -> Context -> String -> IO ()
    evalAndPrint _ _ _ "" = return ()
    evalAndPrint _ defs _ ":defs" =
      flushStr (unlines [ showSourced n | (n,_) <- defs ] ++ "\n")
    evalAndPrint sig defs ctx src =
      case loadTerm sig defs ctx src of
        Left e -> flushStr ("ERROR: " ++ e ++ "\n")
        Right v -> flushStr (pretty v ++ "\n")

replFile :: String -> IO ()
replFile loc = readFile loc >>= repl