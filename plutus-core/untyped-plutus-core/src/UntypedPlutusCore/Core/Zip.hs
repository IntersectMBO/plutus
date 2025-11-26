{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

module UntypedPlutusCore.Core.Zip
  ( pzipWith
  , pzip
  , tzipWith
  , tzip
  ) where

import Control.Monad (void, when)
import Control.Monad.Except (MonadError, throwError)
import Data.Vector
import UntypedPlutusCore.Core.Instance.Eq ()
import UntypedPlutusCore.Core.Type

{-| Zip two programs using a combinator function for annotations.

Throws an error if the input programs are not "equal" modulo annotations.
Note that the function is "left-biased", so in case that the 2 input programs contain `Name`s,
the output program will contain just the `Name`s of the first input program. -}
pzipWith
  :: forall p name uni fun ann1 ann2 ann3 m
   . (p ~ Program name uni fun, (Eq (Term name uni fun ())), MonadError String m)
  => (ann1 -> ann2 -> ann3)
  -> p ann1
  -> p ann2
  -> m (p ann3)
pzipWith f (Program ann1 ver1 t1) (Program ann2 ver2 t2) = do
  when (ver1 /= ver2) $
    throwError "zip: Versions do not match."
  Program (f ann1 ann2) ver1 <$> tzipWith f t1 t2

{-| Zip two terms using a combinator function for annotations.

Throws an error if the input terms are not "equal" modulo annotations.
Note that the function is "left-biased", so in case that the 2 input terms contain `Name`s,
the output term will contain just the `Name`s of the first input term.
TODO: this is not an optimal implementation -}
tzipWith
  :: forall t name uni fun ann1 ann2 ann3 m
   . (t ~ Term name uni fun, Eq (t ()), MonadError String m)
  => (ann1 -> ann2 -> ann3)
  -> t ann1
  -> t ann2
  -> m (t ann3)
tzipWith f term1 term2 = do
  -- Prior establishing t1==t2 avoids the need to check for Eq uni, Eq fun and alpha-equivalence.
  -- Slower this way because we have to re-traverse the terms.
  when (void term1 /= void term2) $
    throwError "zip: Terms do not match."
  go term1 term2
  where
    go :: t ann1 -> t ann2 -> m (t ann3)
    -- MAYBE: some boilerplate could be removed on the following clauses if termAnn was a lens
    go (Constant a1 s1) (Constant a2 _s2) = pure $ Constant (f a1 a2) s1
    go (Builtin a1 f1) (Builtin a2 _f2) = pure $ Builtin (f a1 a2) f1
    go (Var a1 n1) (Var a2 _n2) = pure $ Var (f a1 a2) n1
    go (Error a1) (Error a2) = pure $ Error (f a1 a2)
    -- MAYBE: some boilerplate could be removed here if we used parallel subterm traversals/toListOf
    go (LamAbs a1 n1 t1) (LamAbs a2 _n2 t2) = LamAbs (f a1 a2) n1 <$> go t1 t2
    go (Apply a1 t1a t1b) (Apply a2 t2a t2b) = Apply (f a1 a2) <$> go t1a t2a <*> go t1b t2b
    go (Force a1 t1) (Force a2 t2) = Force (f a1 a2) <$> go t1 t2
    go (Delay a1 t1) (Delay a2 t2) = Delay (f a1 a2) <$> go t1 t2
    go (Constr a1 i1 ts1) (Constr a2 _i2 ts2) = Constr (f a1 a2) i1 <$> zipExactWithM go ts1 ts2
    go (Case a1 t1 vs1) (Case a2 t2 vs2) =
      Case (f a1 a2) <$> go t1 t2 <*> (fromList <$> zipExactWithM go (toList vs1) (toList vs2))
    go _ _ =
      throwError "zip: This should not happen, because we prior established term equality."

    zipExactWithM :: MonadError String n => (a -> b -> n c) -> [a] -> [b] -> n [c]
    zipExactWithM g (a : as) (b : bs) = (:) <$> g a b <*> zipExactWithM g as bs
    zipExactWithM _ [] [] = pure []
    zipExactWithM _ _ _ = throwError "zipExactWithM: not exact"

-- | Zip 2 programs by pairing their annotations
pzip
  :: (p ~ Program name uni fun, Eq (Term name uni fun ()), MonadError String m)
  => p ann1
  -> p ann2
  -> m (p (ann1, ann2))
pzip = pzipWith (,)

-- | Zip 2 terms by pairing their annotations
tzip
  :: (t ~ Term name uni fun, Eq (t ()), MonadError String m)
  => t ann1
  -> t ann2
  -> m (t (ann1, ann2))
tzip = tzipWith (,)
