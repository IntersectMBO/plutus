{-# LANGUAGE GADTs #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TypeOperators #-}

module PlutusIR.Transform.RewriteRules.Common
  ( seqA
  , seqP
  , mkFreshTermLet -- from MkPlc
  , pattern A
  , pattern B
  , pattern I
  ) where

import PlutusCore.Builtin
import PlutusCore.Quote
import PlutusIR
import PlutusIR.Analysis.Builtins
import PlutusIR.Analysis.VarInfo
import PlutusIR.MkPir
import PlutusIR.Purity

{-| A wrapper that can be more easily turned into an infix operator.

e.g. `infixr 5 (***) = seqA binfo vInfo` -}
seqA
  :: (MonadQuote m, Monoid a, ToBuiltinMeaning uni fun)
  => BuiltinsInfo uni fun
  -> VarsInfo tyname Name uni a
  -> (Type tyname uni a, Term tyname Name uni fun a)
  -> m (Term tyname Name uni fun a)
  -> m (Term tyname Name uni fun a)
seqA binfo vinfo (a, aT) y = seqOpt binfo vinfo a aT <*> y

{-| Another "infix" wrapper where second operand is a Haskell pure value.

e.g. `infixr 5 (***) = seqP binfo vInfo` -}
seqP
  :: (MonadQuote m, Monoid a, ToBuiltinMeaning uni fun)
  => BuiltinsInfo uni fun
  -> VarsInfo tyname Name uni a
  -> (Type tyname uni a, Term tyname Name uni fun a)
  -> Term tyname Name uni fun a
  -> m (Term tyname Name uni fun a)
seqP binfo vinfo p y = seqA binfo vinfo p (pure y)

-- | An optimized version to omit call to `seq` if left operand `isPure`.
seqOpt
  :: ( MonadQuote m
     , Monoid a
     , ToBuiltinMeaning uni fun
     , t ~ Term tyname Name uni fun a
     )
  => BuiltinsInfo uni fun
  -> VarsInfo tyname Name uni a
  -> Type tyname uni a
  -- ^ the type of left operand a
  -> t
  -- ^ left operand a
  -> m (t -> t)
  -- ^ how to modify right operand b
seqOpt binfo vinfo aT a
  | isPure binfo vinfo a = pure id
  | otherwise = seqUnOpt aT a

{-| Takes as input a term `a` with its type `aT`,
and constructs a function that expects another term `b`.
When the returned function is applied to a term, the execution of the applied term
would strictly evaluate the first term `a` only for its effects (i.e. ignoring its result)
while returning the result of the second term `b`.

The name is intentionally taken from Haskell's `GHC.Prim.seq`.
Currently, the need for this `seq` "combinator" is in `RewriteRules`,
to trying to retain the effects, that would otherwise be lost if that code was instead considered
completely dead.

Unfortunately, unlike Haskell's `seq`, we need the pass the correct `Type` of `a`,
so as to apply this `seq` combinator. This is usually not a problem because we are generating
code and we should have the type of `a` somewhere available. -}
seqUnOpt
  :: (MonadQuote m, Monoid a, t ~ Term tyname Name uni fun a)
  => Type tyname uni a
  -- ^ the type of left operand a
  -> t
  -- ^ left operand a
  -> m (t -> t)
  -- ^ how to modify right operand b
seqUnOpt aT a = snd <$> mkFreshTermLet aT a

-- Some shorthands for easier pattern-matching when creating rewrite rules
-- TODO: these patterns ignores annotations. Find a better way for easier writing rules that does
-- not ignore annotations e.g. (pattern-PIR-quasiquoters?)
pattern A :: Term tyname name uni fun a -> Term tyname name uni fun a -> Term tyname name uni fun a
pattern A l r <- Apply _ l r
pattern B :: fun -> Term tyname name uni fun a
pattern B b <- Builtin _ b
pattern I :: Term tyname name uni fun a -> Type tyname uni a -> Term tyname name uni fun a
pattern I e t <- TyInst _ e t
