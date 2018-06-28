{-# OPTIONS -Wall #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeSynonymInstances #-}





-- | This module defines how to evaluate terms in the simply typed lambda
-- calculus w/ non-parametric user defined types (eg Bool, Nat).

module PlutusCore.Evaluation where

import Utils.ABT
import Utils.Env
import Utils.Eval
import Utils.Names
import Utils.Pretty (pretty)
import qualified PlutusCore.CKMachine as CK
import PlutusCore.BuiltinEvaluation
import PlutusCore.EvaluatorTypes
import PlutusCore.PatternMatching
import PlutusCore.Term

import Data.Either (isRight)
import qualified Cardano.Crypto.Wallet as CC
import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.State
import qualified Data.ByteString.Lazy as BS






-- | Standard eager evaluation.

instance Eval (Env (Sourced String) Term) Term where
  eval (Var v) =
    return $ Var v
  eval (In (Decname x)) =
    do env <- environment
       case lookup x env of
         Nothing -> throwError $ "Unknown constant/defined term: "
                              ++ showSourced x
         Just m  -> eval m
  eval (In (Let m sc)) =
    do em <- eval (instantiate0 m)
       eval (instantiate sc [em])
  eval (In (Lam sc)) =
    return $ In (Lam sc)
  eval (In (App f a)) =
    do ef <- eval (instantiate0 f)
       ea <- eval (instantiate0 a)
       case ef of
         In (Lam sc) -> eval (instantiate sc [ea])
         _ -> return $ appH ef ea
  eval (In (Con c as)) =
    do eas <- mapM (eval . instantiate0) as
       return $ conH c eas
  eval (In (Case m cs)) =
    do ems <- eval (instantiate0 m)
       case matchClauses cs ems of
         Nothing -> throwError $ "Incomplete pattern match: " ++ pretty (In (Case m cs))
         Just b  -> eval b
  eval (In (Success m)) =
    do em <- eval (instantiate0 m)
       return $ successH em
  eval (In Failure) =
    return $ failureH
  eval (In (Bind m sc)) =
    do em <- eval (instantiate0 m)
       case em of
         In Failure -> return failureH
         In (Success m') -> eval (instantiate sc [instantiate0 m'])
         _ -> throwError $ "Cannot bind a non-computation: " ++ pretty em
  eval (In (PrimData x)) =
    return $ In (PrimData x)
  eval (In (Builtin n0 xs0)) =
    do xs' <- mapM (eval . instantiate0) xs0
       case builtin n0 xs' of
         Left err -> throwError err
         Right x -> return x






tick :: (Num s, MonadState s m) => m ()
tick = modify (subtract 1)

type PetrolEvaluator =
  ReaderT (TransactionInfo,SourcedEnv) (StateT Petrol (Either String))

declEnvironment :: PetrolEvaluator SourcedEnv
declEnvironment = snd <$> ask

signedTransaction :: PetrolEvaluator TransactionInfo
signedTransaction = fst <$> ask

instance MEval
           (TransactionInfo,SourcedEnv)
           String
           PetrolEvaluator
           Term where
  meval m0 =
    do ptrl <- get
       if ptrl <= 0
         then throwError $ "Out of petrol when evaluating " ++ pretty m0
         else go m0
    where
      go :: Term -> PetrolEvaluator Term
      go (Var v) =
        do tick
           return $ Var v
      go (In (Decname x)) =
        do tick
           env <- declEnvironment
           case lookup x env of
             Nothing -> throwError $ "Unknown constant/defined term: "
                                  ++ showSourced x
             Just m  -> return m
      go (In (Let m sc)) =
        do tick 
           em <- meval (instantiate0 m)
           meval (instantiate sc [em])
      go (In (Lam sc)) =
        do tick
           return $ In (Lam sc)
      go (In (App f a)) =
        do tick
           ef <- meval (instantiate0 f)
           ea <- meval (instantiate0 a)
           case ef of
             In (Lam sc) ->
               meval (instantiate sc [ea])
             _ -> return $ appH ef ea
      go (In (Con c as)) =
        do tick
           eas <- mapM (meval . instantiate0) as
           return $ conH c eas
      go (In (Case m cs)) =
        do tick
           em <- meval (instantiate0 m)
           case matchClauses cs em of
             Nothing -> throwError $ "Incomplete pattern match: "
                                  ++ pretty (In (Case m cs))
             Just b  -> meval b
      go (In (Success m)) =
        do tick
           em <- meval (instantiate0 m)
           return $ successH em
      go (In Failure) =
        do tick
           return failureH
      go (In (Bind m sc)) =
        do tick
           em <- meval (instantiate0 m)
           case em of
             In Failure -> return failureH
             In (Success m') -> meval (instantiate sc [instantiate0 m'])
             _ -> throwError $ "Cannot bind a non-computation: " ++ pretty em
      go (In (PrimData x)) =
        do tick
           return $ In (PrimData x)
      go (In (Builtin n0 xs0)) =
        do tick
           xs' <- mapM (meval . instantiate0) xs0
           case builtin n0 xs' of
             Left err -> throwError err
             Right x -> return x
      




evaluate
  :: TransactionInfo -> SourcedEnv -> Petrol -> Term -> Either String Term
evaluate txinfo env ptrl m =
  CK.evaluate txinfo env ptrl m
  {-
  let evlt = meval m :: PetrolEvaluator Term
      result = runStateT (runReaderT evlt (txinfo,env)) ptrl
  in fst <$> result
  -}

----------------------------------------------------------------------------
-- Crypto
----------------------------------------------------------------------------

publicKeyLength, signatureLength, chainCodeLength :: Int
publicKeyLength = 32
signatureLength = 64
chainCodeLength = 32

verify :: BS.ByteString -> BS.ByteString -> BS.ByteString -> Bool
verify key val sig = isRight $ do
  key' <- CC.xpub (BS.toStrict key)
  sig' <- CC.xsignature (BS.toStrict sig)
  case CC.verify key' (BS.toStrict val) sig' of
    True  -> Right ()
    False -> Left ""