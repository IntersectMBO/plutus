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
import PlutusCore.Term

import qualified Crypto.Sign.Ed25519 as Ed25519
import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.State
import Crypto.Hash
import qualified Data.ByteString.Lazy as BS
import qualified Data.Binary as B
import Data.List (intercalate)
import qualified Data.ByteArray as BA





-- | Pattern matching for case expressions.

matchPattern :: Pattern -> Term -> Maybe [Term]
matchPattern (Var _) v = Just [v]
matchPattern (In (ConPat c ps)) (In (Con c' as))
  | c == c' && length ps == length as =
    fmap concat (zipWithM matchPattern (map body ps) (map body as))
matchPattern (In (PrimPat x)) (In (PrimData y))
  | x == y = Just []
matchPattern _ _ = Nothing

matchPatterns :: [Pattern] -> [Term] -> Maybe [Term]
matchPatterns ps zs = fmap concat (zipWithM matchPattern ps zs)

matchClauses :: [Clause] -> [Term] -> Maybe Term
matchClauses [] _ =
  Nothing
matchClauses (Clause pscs sc:cs) vs =
  case matchPatterns (map body pscs) vs of
    Nothing -> matchClauses cs vs
    Just xs -> Just (instantiate sc xs)





-- | Standard eager evaluation.

instance Eval (Env (Sourced String) Term) Term where
  eval (Var v) =
    return $ Var v
  eval (In (Decname x _)) =
    do env <- environment
       case lookup x env of
         Nothing -> throwError $ "Unknown constant/defined term: "
                              ++ showSourced x
         Just m  -> return m
  eval (In (Let m sc)) =
    do em <- eval (instantiate0 m)
       eval (instantiate sc [em])
  eval (In (Lam t sc)) =
    return $ In (Lam t sc)
  eval (In (App f a)) =
    do ef <- eval (instantiate0 f)
       ea <- eval (instantiate0 a)
       case ef of
         In (Lam _ sc) -> eval (instantiate sc [ea])
         _ -> return $ appH ef ea
  eval (In (Con c as)) =
    do eas <- mapM (eval . instantiate0) as
       return $ conH c eas
  eval (In (Case ms cs)) =
    do ems <- mapM (eval . instantiate0) ms
       case matchClauses cs ems of
         Nothing -> throwError $ "Incomplete pattern match: " ++ pretty (In (Case ms cs))
         Just b  -> eval b
  eval (In (Success m)) =
    do em <- eval (instantiate0 m)
       return $ successH em
  eval (In (Failure t)) =
    return $ failureH t
  eval (In (Bind m sc)) =
    do em <- eval (instantiate0 m)
       case em of
         In (Failure t) -> return $ failureH t
         In (Success m') -> eval (instantiate sc [instantiate0 m'])
         _ -> throwError $ "Cannot bind a non-computation: " ++ pretty em
  eval (In (PrimData x)) =
    return $ In (PrimData x)
  eval (In (Builtin n0 xs0)) =
    do xs' <- mapM (eval . instantiate0) xs0
       builtin n0 xs'
    where
      builtin :: String
              -> [Term]
              -> Evaluator (Env (Sourced String) Term) Term
      builtin "addInt" xs =
        case xs of
          [In (PrimData (PrimInt x)), In (PrimData (PrimInt y))] ->
            return $ In (PrimData (PrimInt (x + y)))
          _ ->
            throwError $ "Incorrect arguments for builtin addInt: "
                      ++ intercalate "," (map pretty xs)
      builtin "subtractInt" xs =
        case xs of
          [In (PrimData (PrimInt x)), In (PrimData (PrimInt y))] ->
            return $ In (PrimData (PrimInt (x - y)))
          _ ->
            throwError $ "Incorrect arguments for builtin subtractInt: "
                      ++ intercalate "," (map pretty xs)
      builtin "multiplyInt" xs =
        case xs of
          [In (PrimData (PrimInt x)), In (PrimData (PrimInt y))] ->
            return $ In (PrimData (PrimInt (x * y)))
          _ ->
            throwError $ "Incorrect arguments for builtin multiplyInt: "
                      ++ intercalate "," (map pretty xs)
      builtin "divideInt" xs =
        case xs of
          [In (PrimData (PrimInt x)), In (PrimData (PrimInt y))] ->
            return $ In (PrimData (PrimInt (div x y)))
          _ ->
            throwError $ "Incorrect arguments for builtin divideInt: "
                      ++ intercalate "," (map pretty xs)
      builtin "remainderInt" xs =
        case xs of
          [In (PrimData (PrimInt x)), In (PrimData (PrimInt y))] ->
            return $ In (PrimData (PrimInt (mod x y)))
          _ ->
            throwError $ "Incorrect arguments for builtin remainderInt: "
                      ++ intercalate "," (map pretty xs)
      builtin "lessThanInt" xs =
        case xs of
          [In (PrimData (PrimInt x)), In (PrimData (PrimInt y))] ->
            return $ if x < y then conH "True" [] else conH "False" []
          _ ->
            throwError $ "Incorrect arguments for builtin lessThanInt: "
                      ++ intercalate "," (map pretty xs)
      builtin "equalsInt" xs =
        case xs of
          [In (PrimData (PrimInt x)), In (PrimData (PrimInt y))] ->
            return $ if x == y then conH "True" [] else conH "False" []
          _ ->
            throwError $ "Incorrect arguments for builtin equalsInt: "
                      ++ intercalate "," (map pretty xs)
      builtin "intToFloat" xs =
        case xs of
          [In (PrimData (PrimInt x))] ->
            return $ In (PrimData (PrimFloat (fromInteger (toInteger x))))
          _ ->
            throwError $ "Incorrect arguments for builtin intToFloat: "
                      ++ intercalate "," (map pretty xs)
      builtin "intToByteString" xs =
        case xs of
          [In (PrimData (PrimInt x))] ->
            return $ In (PrimData (PrimByteString (B.encode x)))
          _ ->
            throwError
              $ "Incorrect arguments for builtin intToBytestring: "
             ++ intercalate "," (map pretty xs)
      builtin "addFloat" xs =
        case xs of
          [In (PrimData (PrimFloat x)), In (PrimData (PrimFloat y))] ->
            return $ In (PrimData (PrimFloat (x + y)))
          _ ->
            throwError $ "Incorrect arguments for builtin addFloat: "
                      ++ intercalate "," (map pretty xs)
      builtin "subtractFloat" xs =
        case xs of
          [In (PrimData (PrimFloat x)), In (PrimData (PrimFloat y))] ->
            return $ In (PrimData (PrimFloat (x - y)))
          _ ->
            throwError $ "Incorrect arguments for builtin subtractFloat: "
                      ++ intercalate "," (map pretty xs)  
      builtin "multiplyFloat" xs =
        case xs of
          [In (PrimData (PrimFloat x)), In (PrimData (PrimFloat y))] ->
            return $ In (PrimData (PrimFloat (x * y)))
          _ ->
            throwError $ "Incorrect arguments for builtin multiplyFloat: "
                      ++ intercalate "," (map pretty xs)
      builtin "divideFloat" xs =
        case xs of
          [In (PrimData (PrimFloat x)), In (PrimData (PrimFloat y))] ->
            return $ In (PrimData (PrimFloat (x / y)))
          _ ->
            throwError $ "Incorrect arguments for builtin divideFloat: "
                      ++ intercalate "," (map pretty xs)
      builtin "lessThanFloat" xs =
        case xs of
          [In (PrimData (PrimFloat x)), In (PrimData (PrimFloat y))] ->
            return $ if x < y then conH "True" [] else conH "False" []
          _ ->
            throwError $ "Incorrect arguments for builtin lessThanFloat: "
                      ++ intercalate "," (map pretty xs)
      builtin "equalsFloat" xs =
        case xs of
          [In (PrimData (PrimFloat x)), In (PrimData (PrimFloat y))] ->
            return $ if x == y then conH "True" [] else conH "False" []
          _ ->
            throwError $ "Incorrect arguments for builtin equalsFloat: "
                      ++ intercalate "," (map pretty xs)
      builtin "ceiling" xs =
        case xs of
          [In (PrimData (PrimFloat x))] ->
            return $ In (PrimData (PrimInt (ceiling x)))
          _ ->
            throwError $ "Incorrect arguments for builtin ceiling: "
                      ++ intercalate "," (map pretty xs)
      builtin "floor" xs =
        case xs of
          [In (PrimData (PrimFloat x))] ->
            return $ In (PrimData (PrimInt (floor x)))
          _ ->
            throwError $ "Incorrect arguments for builtin floor: "
                      ++ intercalate "," (map pretty xs)
      builtin "round" xs =
        case xs of
          [In (PrimData (PrimFloat x))] ->
            return $ In (PrimData (PrimInt (round x)))
          _ ->
            throwError $ "Incorrect arguments for builtin round: "
                      ++ intercalate "," (map pretty xs)
      builtin "concatenate" xs =
        case xs of
          [ In (PrimData (PrimByteString x))
            , In (PrimData (PrimByteString y))
            ] ->
            return $ In (PrimData (PrimByteString (BS.concat [x,y])))
          _ ->
            throwError $ "Incorrect arguments for builtin concatenate: "
                      ++ intercalate "," (map pretty xs)
      builtin "drop" xs =
        case xs of
          [ In (PrimData (PrimInt x))
            , In (PrimData (PrimByteString y))
            ] ->
            return $ In (PrimData (PrimByteString (BS.drop (fromIntegral x) y)))
          _ ->
            throwError $ "Incorrect arguments for builtin drop: "
                      ++ intercalate "," (map pretty xs)
      builtin "take" xs =
        case xs of
          [ In (PrimData (PrimInt x))
            , In (PrimData (PrimByteString y))
            ] ->
            return $ In (PrimData (PrimByteString (BS.take (fromIntegral x) y)))
          _ ->
            throwError $ "Incorrect arguments for builtin take: "
                      ++ intercalate "," (map pretty xs)
      builtin "sha2_256" xs =
        case xs of
          [In (PrimData (PrimByteString x))] ->
            return $ In (PrimData
                          (PrimByteString
                            (BS.pack
                              (BA.unpack (hash (BS.toStrict x) :: Digest SHA256)))))
          _ ->
            throwError $ "Incorrect arguments for builtin sha2_256: "
                      ++ intercalate "," (map pretty xs)
      builtin "sha3_256" xs =
        case xs of
          [In (PrimData (PrimByteString x))] ->
            return $ In (PrimData
                          (PrimByteString
                            (BS.pack
                              (BA.unpack (hash (BS.toStrict x) :: Digest SHA3_256)))))
          _ ->
            throwError $ "Incorrect arguments for builtin sha2_256: "
                      ++ intercalate "," (map pretty xs)
      builtin "equalsByteString" xs =
        case xs of
          [ In (PrimData (PrimByteString x))
            , In (PrimData (PrimByteString y))
            ] ->
            return $ if x == y then conH "True" [] else conH "False" []
          _ ->
            throwError $ "Incorrect arguments for builtin equalsByteString: "
                      ++ intercalate "," (map pretty xs)     
      builtin n _ =
        throwError $ "No builtin named " ++ n




newtype TransactionInfo = TransactionInfo BS.ByteString

newtype Petrol = Petrol Int
  deriving (Show,Num,Eq,Ord)

type SourcedEnv = Env (Sourced String) Term

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
      go (In (Decname x _)) =
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
      go (In (Lam t sc)) =
        do tick
           return $ In (Lam t sc)
      go (In (App f a)) =
        do tick
           ef <- meval (instantiate0 f)
           ea <- meval (instantiate0 a)
           case ef of
             In (Lam _ sc) ->
               meval (instantiate sc [ea])
             _ -> return $ appH ef ea
      go (In (Con c as)) =
        do tick
           eas <- mapM (meval . instantiate0) as
           return $ conH c eas
      go (In (Case ms cs)) =
        do tick
           ems <- mapM (meval . instantiate0) ms
           case matchClauses cs ems of
             Nothing -> throwError $ "Incomplete pattern match: "
                                  ++ pretty (In (Case ms cs))
             Just b  -> meval b
      go (In (Success m)) =
        do tick
           em <- meval (instantiate0 m)
           return $ successH em
      go (In (Failure t)) =
        do tick
           return $ failureH t
      go (In (Bind m sc)) =
        do tick
           em <- meval (instantiate0 m)
           case em of
             In (Failure t) -> return $ failureH t
             In (Success m') -> meval (instantiate sc [instantiate0 m'])
             _ -> throwError $ "Cannot bind a non-computation: " ++ pretty em
      go (In (PrimData x)) =
        do tick
           return $ In (PrimData x)
      go (In (Builtin n0 xs0)) =
        do tick
           xs' <- mapM (meval . instantiate0) xs0
           builtin n0 xs'
      
      builtin :: String -> [Term] -> PetrolEvaluator Term
      builtin "addInt" xs =
        case xs of
          [In (PrimData (PrimInt x)), In (PrimData (PrimInt y))] ->
            return $ In (PrimData (PrimInt (x + y)))
          _ ->
            throwError $ "Incorrect arguments for builtin addInt: "
                      ++ intercalate "," (map pretty xs)
      builtin "subtractInt" xs =
        case xs of
          [In (PrimData (PrimInt x)), In (PrimData (PrimInt y))] ->
            return $ In (PrimData (PrimInt (x - y)))
          _ ->
            throwError $ "Incorrect arguments for builtin subtractInt: "
                      ++ intercalate "," (map pretty xs)
      builtin "multiplyInt" xs =
        case xs of
          [In (PrimData (PrimInt x)), In (PrimData (PrimInt y))] ->
            return $ In (PrimData (PrimInt (x * y)))
          _ ->
            throwError $ "Incorrect arguments for builtin multiplyInt: "
                      ++ intercalate "," (map pretty xs)
      builtin "divideInt" xs =
        case xs of
          [In (PrimData (PrimInt x)), In (PrimData (PrimInt y))] ->
            return $ In (PrimData (PrimInt (div x y)))
          _ ->
            throwError $ "Incorrect arguments for builtin divideInt: "
                      ++ intercalate "," (map pretty xs)
      builtin "remainderInt" xs =
        case xs of
          [In (PrimData (PrimInt x)), In (PrimData (PrimInt y))] ->
            return $ In (PrimData (PrimInt (mod x y)))
          _ ->
            throwError $ "Incorrect arguments for builtin remainderInt: "
                      ++ intercalate "," (map pretty xs)
      builtin "lessThanInt" xs =
        case xs of
          [In (PrimData (PrimInt x)), In (PrimData (PrimInt y))] ->
            return $ if x < y then conH "True" [] else conH "False" []
          _ ->
            throwError $ "Incorrect arguments for builtin lessThanInt: "
                      ++ intercalate "," (map pretty xs)
      builtin "equalsInt" xs =
        case xs of
          [In (PrimData (PrimInt x)), In (PrimData (PrimInt y))] ->
            return $ if x == y then conH "True" [] else conH "False" []
          _ ->
            throwError $ "Incorrect arguments for builtin equalsInt: "
                      ++ intercalate "," (map pretty xs)
      builtin "intToFloat" xs =
        case xs of
          [In (PrimData (PrimInt x))] ->
            return $ In (PrimData (PrimFloat (fromInteger (toInteger x))))
          _ ->
            throwError $ "Incorrect arguments for builtin intToFloat: "
                      ++ intercalate "," (map pretty xs)
      builtin "intToByteString" xs =
        case xs of
          [In (PrimData (PrimInt x))] ->
            return $ In (PrimData (PrimByteString (B.encode x)))
          _ ->
            throwError
              $ "Incorrect arguments for builtin intToBytestring: "
             ++ intercalate "," (map pretty xs)
      builtin "addFloat" xs =
        case xs of
          [In (PrimData (PrimFloat x)), In (PrimData (PrimFloat y))] ->
            return $ In (PrimData (PrimFloat (x + y)))
          _ ->
            throwError $ "Incorrect arguments for builtin addFloat: "
                      ++ intercalate "," (map pretty xs)
      builtin "subtractFloat" xs =
        case xs of
          [In (PrimData (PrimFloat x)), In (PrimData (PrimFloat y))] ->
            return $ In (PrimData (PrimFloat (x - y)))
          _ ->
            throwError $ "Incorrect arguments for builtin subtractFloat: "
                      ++ intercalate "," (map pretty xs)  
      builtin "multiplyFloat" xs =
        case xs of
          [In (PrimData (PrimFloat x)), In (PrimData (PrimFloat y))] ->
            return $ In (PrimData (PrimFloat (x * y)))
          _ ->
            throwError $ "Incorrect arguments for builtin multiplyFloat: "
                      ++ intercalate "," (map pretty xs)
      builtin "divideFloat" xs =
        case xs of
          [In (PrimData (PrimFloat x)), In (PrimData (PrimFloat y))] ->
            return $ In (PrimData (PrimFloat (x / y)))
          _ ->
            throwError $ "Incorrect arguments for builtin divideFloat: "
                      ++ intercalate "," (map pretty xs)
      builtin "lessThanFloat" xs =
        case xs of
          [In (PrimData (PrimFloat x)), In (PrimData (PrimFloat y))] ->
            return $ if x < y then conH "True" [] else conH "False" []
          _ ->
            throwError $ "Incorrect arguments for builtin lessThanFloat: "
                      ++ intercalate "," (map pretty xs)
      builtin "equalsFloat" xs =
        case xs of
          [In (PrimData (PrimFloat x)), In (PrimData (PrimFloat y))] ->
            return $ if x == y then conH "True" [] else conH "False" []
          _ ->
            throwError $ "Incorrect arguments for builtin equalsFloat: "
                      ++ intercalate "," (map pretty xs)
      builtin "ceiling" xs =
        case xs of
          [In (PrimData (PrimFloat x))] ->
            return $ In (PrimData (PrimInt (ceiling x)))
          _ ->
            throwError $ "Incorrect arguments for builtin ceiling: "
                      ++ intercalate "," (map pretty xs)
      builtin "floor" xs =
        case xs of
          [In (PrimData (PrimFloat x))] ->
            return $ In (PrimData (PrimInt (floor x)))
          _ ->
            throwError $ "Incorrect arguments for builtin floor: "
                      ++ intercalate "," (map pretty xs)
      builtin "round" xs =
        case xs of
          [In (PrimData (PrimFloat x))] ->
            return $ In (PrimData (PrimInt (round x)))
          _ ->
            throwError $ "Incorrect arguments for builtin round: "
                      ++ intercalate "," (map pretty xs)
      builtin "concatenate" xs =
        case xs of
          [ In (PrimData (PrimByteString x))
            , In (PrimData (PrimByteString y))
            ] ->
            return $ In (PrimData (PrimByteString (BS.concat [x,y])))
          _ ->
            throwError $ "Incorrect arguments for builtin concatenate: "
                      ++ intercalate "," (map pretty xs)
      builtin "drop" xs =
        case xs of
          [ In (PrimData (PrimInt x))
            , In (PrimData (PrimByteString y))
            ] ->
            return $ In (PrimData (PrimByteString (BS.drop (fromIntegral x) y)))
          _ ->
            throwError $ "Incorrect arguments for builtin drop: "
                      ++ intercalate "," (map pretty xs)
      builtin "take" xs =
        case xs of
          [ In (PrimData (PrimInt x))
            , In (PrimData (PrimByteString y))
            ] ->
            return $ In (PrimData (PrimByteString (BS.take (fromIntegral x) y)))
          _ ->
            throwError $ "Incorrect arguments for builtin take: "
                      ++ intercalate "," (map pretty xs)
      builtin "sha2_256" xs =
        case xs of
          [In (PrimData (PrimByteString x))] ->
            return $ In (PrimData
                          (PrimByteString
                            (BS.pack
                              (BA.unpack (hash (BS.toStrict x) :: Digest SHA256)))))
          _ ->
            throwError $ "Incorrect arguments for builtin sha2_256: "
                      ++ intercalate "," (map pretty xs)
      builtin "sha3_256" xs =
        case xs of
          [In (PrimData (PrimByteString x))] ->
            return $ In (PrimData
                          (PrimByteString
                            (BS.pack
                              (BA.unpack (hash (BS.toStrict x) :: Digest SHA3_256)))))
          _ ->
            throwError $ "Incorrect arguments for builtin sha2_256: "
                      ++ intercalate "," (map pretty xs)
      builtin "equalsByteString" xs =
        case xs of
          [ In (PrimData (PrimByteString x))
            , In (PrimData (PrimByteString y))
            ] ->
            return $ if x == y then conH "True" [] else conH "False" []
          _ ->
            throwError $ "Incorrect arguments for builtin equalsByteString: "
                      ++ intercalate "," (map pretty xs)     
      builtin "verifySignature" xs =
        case xs of
          [ In (PrimData (PrimByteString key))
            , In (PrimData (PrimByteString val))
            , In (PrimData (PrimByteString sig))
            ] ->
            return $ let key' = Ed25519.PublicKey (BS.toStrict key)
                         sig' = Ed25519.Signature (BS.toStrict sig)
                         val' = BS.toStrict val
                     in if BS.length key == 32 && BS.length sig == 64 &&
                           Ed25519.dverify key' val' sig'
                          then conH "True" []
                          else conH "False" []
          _ ->
            throwError $ "Incorrect arguments for builtin verifySignature: "
                      ++ intercalate "," (map pretty xs)     
      builtin "transactionInfo" xs =
        case xs of
          [] -> do
            TransactionInfo txInfo <- fst <$> ask
            return $ successH
                       (primByteStringH txInfo)
          _ ->
            throwError $ "Incorrect arguments for builtin transactionInfo: "
                      ++ intercalate "," (map pretty xs)     
      builtin n _ =
        throwError $ "No builtin named " ++ n



evaluate
  :: TransactionInfo -> SourcedEnv -> Petrol -> Term -> Either String Term
evaluate txinfo env ptrl m =
  let evlt = meval m :: PetrolEvaluator Term
      result = runStateT (runReaderT evlt (txinfo,env)) ptrl
  in fst <$> result