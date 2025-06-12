-- Copyright 2023 Lennart Augustsson
-- See LICENSE file for full license.
{-# OPTIONS_GHC -Wno-type-defaults -Wno-noncanonical-monad-instances #-}
{-# LANGUAGE FunctionalDependencies #-}
module Text.ParserComb(
  Prsr, runPrsr,
  satisfy, satisfyM,
  many, optional, some,
  sepBy, sepBy1,
  sepEndBy, sepEndBy1,
  (<?>),
  (<<),
  --notFollowedBy,
  --lookAhead,
  nextToken,
  LastFail(..),
  TokenMachine(..),
  mapTokenState,
  ) where
import qualified Prelude(); import MHSPrelude hiding (fail)
import Control.Applicative
import Control.Monad.Fail as F
import Control.Monad

data LastFail t
  = LastFail Int [t] [String]
  deriving (Show)

maxInt :: Int
maxInt = 1000000000

noFail :: forall t . LastFail t
noFail = LastFail maxInt [] []

longest :: forall t . LastFail t -> LastFail t -> LastFail t
longest lf1@(LastFail l1 t1 x1) lf2@(LastFail l2 _ x2)
  | l1 < l2   = lf1
  | l2 < l1   = lf2
  | otherwise = LastFail l1 t1 (x1 ++ x2)

class TokenMachine tm t | tm -> t where
  tmNextToken :: tm -> (t, tm)
  tmRawTokens :: tm -> [t]

tmLeft :: forall tm t . TokenMachine tm t => tm -> Int
tmLeft = length . tmRawTokens

firstToken :: forall tm t . TokenMachine tm t => tm -> [t]
firstToken tm =
  case tmNextToken tm of
    (t, _) -> [t]

data Res tm t a = Success a tm (LastFail t) | Failure (LastFail t)
  --deriving (Show)

newtype Prsr tm t a = P (tm -> Res tm t a)
--instance Show (Prsr s t a) where show _ = "<<Prsr>>"

runP :: forall tm t a . Prsr tm t a -> (tm -> Res tm t a)
runP (P p) = p

mapTokenState :: forall tm t . (tm -> tm) -> Prsr tm t ()
mapTokenState f = P (\tm -> Success () (f tm) noFail)

instance Functor (Prsr tm t) where
  fmap f p = P $ \t ->
    case runP p t of
      Success a u lf -> Success (f a) u lf
      Failure lf -> Failure lf

instance Applicative (Prsr tm t) where
  pure a = P $ \t -> Success a t noFail
  f <*> a = P $ \t ->
    case runP f t of
      Failure lf -> Failure lf
      Success f' t' lff ->
        case runP a t' of
          Failure lfa -> Failure (longest lff lfa)
          Success a' t'' lfa -> Success (f' a') t'' (longest lff lfa)
-- Hugs does not have *> here
--  (*>) p k = p >>= \ _ -> k

(<<) :: Prsr tm t a -> Prsr tm t b -> Prsr tm t a
(<<) f a = P $ \t ->
    case runP f t of
      Failure lf -> Failure lf
      Success f' t' lff ->
        case runP a t' of
          Failure lfa -> Failure (longest lff lfa)
          Success _ t'' lfa -> Success f' t'' (longest lff lfa)

instance Monad (Prsr tm t) where
  (>>=) p k = P $ \t ->
    case runP p t of
      Success a u lfa ->
        case runP (k a) u of
          Success b v lfb -> Success b v (longest lfa lfb)
          Failure lfb -> Failure (longest lfa lfb)
      Failure lf -> Failure lf
  (>>) p k = p >>= const k
  return = pure

instance TokenMachine tm t => MonadFail (Prsr tm t) where
  fail m = P $ \ts -> Failure (LastFail (tmLeft ts) (firstToken ts) [m])

instance TokenMachine tm t => Alternative (Prsr tm t) where
  empty = F.fail "empty"

  (<|>) p q = P $ \ t ->
    case runP p t of
      Failure lfa ->
        case runP q t of
          Success b v lfb -> Success b v (longest lfa lfb)
          Failure lfb -> Failure (longest lfa lfb)
      r -> r

instance TokenMachine tm t => MonadPlus (Prsr tm t) where
  mzero = fail "mzero"
  mplus = (<|>)

satisfy :: forall tm t . TokenMachine tm t => String -> (t -> Bool) -> Prsr tm t t
satisfy msg f = P $ \ acs ->
  case tmNextToken acs of
    (c, cs) | f c -> Success c cs noFail
    _ -> Failure (LastFail (tmLeft acs) (firstToken acs) [msg])

satisfyM :: forall tm t a . TokenMachine tm t => String -> (t -> Maybe a) -> Prsr tm t a
satisfyM msg f = P $ \ acs ->
  case tmNextToken acs of
    (c, cs) | Just a <- f c -> Success a cs noFail
    _ -> Failure (LastFail (tmLeft acs) (firstToken acs) [msg])

infixl 9 <?>
(<?>) :: forall tm t a . Prsr tm t a -> String -> Prsr tm t a
(<?>) p e = P $ \ t ->
--  trace ("<?> " ++ show e) $
  case runP p t of
    Failure (LastFail l ts _) -> Failure (LastFail l ts [e])
    s -> s

{-
lookAhead :: forall tm t a . TokenMachine tm t => Prsr tm t a -> Prsr tm t ()
lookAhead p = P $ \ t ->
  case runP p t of
    Many [] (LastFail l ts xs) -> Many [] (LastFail l (take 1 ts) xs)
    _                          -> Many [((), t)] noFail
-}

nextToken :: forall tm t . TokenMachine tm t => Prsr tm t t
nextToken = P $ \ cs ->
  case tmNextToken cs of
    (c, _) -> Success c cs noFail

{-
eof :: forall tm t . TokenMachine tm t => Prsr tm t ()
eof = P $ \ t@(cs, _) ->
  case tmNextToken cs of
    Nothing -> Many [((), t)] noFail
    Just _  -> Many [] (LastFail (tmLeft cs) (firstToken cs) ["eof"])
-}

{-
notFollowedBy :: forall t a . Prsr t a -> Prsr t ()
notFollowedBy p = P $ \ t@(ts,_) ->
  case runP p t of
    Many [] _ -> Many [((), t)] noFail
    _         -> Many [] (LastFail (length ts) (take 1 ts) ["!"])
-}

runPrsr :: forall tm t a . --X(Show a, Show s) =>
           Prsr tm t a -> tm -> Either (LastFail t) a
runPrsr (P p) f =
  case p f of
    Failure lf    -> Left lf
    Success a _ _ -> Right a

-------------------------------

sepBy1 :: TokenMachine tm t => Prsr tm t a -> Prsr tm t sep -> Prsr tm t [a]
sepBy1 p sep = (:) <$> p <*> many (sep >> p)

sepBy :: TokenMachine tm t => Prsr tm t a -> Prsr tm t sep -> Prsr tm t [a]
sepBy p sep = sepBy1 p sep <|> pure []

sepEndBy :: TokenMachine tm t => Prsr tm t a -> Prsr tm t sep -> Prsr tm t [a]
sepEndBy p sep = sepEndBy1 p sep <|> pure []

sepEndBy1 :: TokenMachine tm t => Prsr tm t a -> Prsr tm t sep -> Prsr tm t [a]
sepEndBy1 p sep = (:) <$> p <*> ((sep >> sepEndBy p sep) <|> pure [])
