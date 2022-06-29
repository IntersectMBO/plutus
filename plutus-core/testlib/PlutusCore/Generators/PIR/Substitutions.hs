{-# LANGUAGE BangPatterns          #-}
{-# LANGUAGE ConstraintKinds       #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE DeriveAnyClass        #-}
{-# LANGUAGE DeriveFunctor         #-}
{-# LANGUAGE DerivingVia           #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE ImportQualifiedPost   #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NumericUnderscores    #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE PatternSynonyms       #-}
{-# LANGUAGE RecordWildCards       #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE TupleSections         #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE UndecidableInstances  #-}
{-# LANGUAGE ViewPatterns          #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}
{-# OPTIONS_GHC -Wno-partial-type-signatures #-}

module PlutusCore.Generators.PIR.Substitutions where

import Control.Monad.Except

import Data.Either
import Data.Map (Map)
import Data.Map qualified as Map
import Data.Maybe
import Data.Set (Set)
import Data.Set qualified as Set
import GHC.Stack
import Test.QuickCheck

import PlutusCore.Default
import PlutusCore.Name
import PlutusCore.Pretty
import PlutusIR
import PlutusIR.Subst

import PlutusCore.Generators.PIR.GenerateTypes
import PlutusCore.Generators.PIR.Utils

-- | Perform unification. Sound but not complete.
unifyType :: Map TyName (Kind ())
          -- ^ Type context
          -> Set TyName
          -- ^ Flexible variables (can be unified)
          -> Map TyName (Type TyName DefaultUni ())
          -- ^ Existing substitution (usually empty)
          -> Type TyName DefaultUni ()
          -- ^ `t1`
          -> Type TyName DefaultUni ()
          -- ^ `t2`
          -> Either String (Map TyName (Type TyName DefaultUni ()))
          -- ^ either an error or a substitution with domain `flex` that unifies `t1` and `t2`
unifyType ctx flex sub a b = go sub Set.empty (normalizeTy a) (normalizeTy b)
  where
    go sub locals a b =
      case (a, b) of
        (TyVar _ (flip Map.lookup sub -> Just a'), _ ) -> go sub locals a' b
        (_, TyVar _ (flip Map.lookup sub -> Just b') ) -> go sub locals a b'
        (TyVar _ x, TyVar _ y) | x == y                -> pure sub
        (TyVar _ x, b) | validSolve x b                -> pure $ Map.insert x b sub
        (a, TyVar _ y) | validSolve y a                -> pure $ Map.insert y a sub
        (TyFun _ a1 a2, TyFun _ b1 b2 )                -> unifies sub locals [(a1, b1), (a2, b2)]
        (TyApp _ a1 a2, TyApp _ b1 b2 )                -> unifies sub locals [(a1, b1), (a2, b2)]
        (TyBuiltin _ c1, TyBuiltin _ c2) | c1 == c2    -> pure sub
        (TyForall _ x k a', TyForall _ y k' b')
          | k == k'                                    -> go sub (Set.insert z locals)
                                                                 (renameType x z a')
                                                                 (renameType y z b')
          where z = freshenTyName (locals <> Map.keysSet ctx) x
        (TyLam _ x k a', TyLam _ y k' b')
          | k == k'                                    -> go sub (Set.insert z locals)
                                                                 (renameType x z a')
                                                                 (renameType y z b')
          where z = freshenTyName (locals <> Map.keysSet ctx) x
        (TyIFix _ a1 a2, TyIFix _ b1 b2 )              -> unifies sub locals [(a1, b1), (a2, b2)]
        (a, b)                                         ->
          Left $ concat
            [ "Failed to unify\n\n"
            , display a
            , "\n\n and\n\n"
            , display b
            , "\n\n"
            ]
      where
        -- TODO: Eitherify that.
        -- Check that in the current context we can solve variable z to type ty.
        validSolve z ty = and [ Set.member z flex -- z must be a "meta variable"
                              -- z can't be a locally bound variable
                              , not $ Set.member z locals
                              -- we can't solve z by changing it to a type
                              -- where `z` is free in the type.
                              , not $ Set.member z fvs
                              -- The solve has to be well scoped
                              , isRight $ checkKind ctx ty (ctx Map.! z)
                              -- We can't capture a locally bound variable
                              , null $ Set.intersection fvs locals ]
                              where fvs = fvTypeR sub ty

    unifies sub _ [] = pure sub
    unifies sub locals ((a, b) : abs) = do
      sub1 <- go sub locals a b
      unifies sub1 locals abs

-- | Parallel substitution
parSubstType :: Map TyName (Type TyName DefaultUni ())
             -> Type TyName DefaultUni ()
             -> Type TyName DefaultUni ()
parSubstType = substType' False

-- CODE REVIEW: this function is a bit strange and I don't like it. Ideas welcome for how to
-- do this better. It basically deals with the fact that we want to be careful when substituting
-- the datatypes that escape from a term into the type. It's yucky but it works.
--
-- This might not be a welcome opinion, but working with this stuff exposes some of
-- the shortcomings of the current PIR design. It would be cleaner if a PIR program was a list
-- of declarations and datatype declarations weren't in terms.
-- TODO: Is this actually doing anything other than what we already do in other substitution functions?!
substEscape :: Set TyName
            -> Map TyName (Type TyName DefaultUni ())
            -> Type TyName DefaultUni ()
            -> Type TyName DefaultUni ()
substEscape fv sub ty = case ty of
  TyVar _ x        -> maybe ty (substEscape fv sub) (Map.lookup x sub)
  TyFun _ a b      -> TyFun () (substEscape fv sub a) (substEscape fv sub b)
  TyApp _ a b      -> TyApp () (substEscape fv sub a) (substEscape fv sub b)
  TyLam _ x k b    -> TyLam () x k $ substEscape (Set.insert x fv) sub b
  TyForall _ x k b -> TyForall () x k $ substEscape (Set.insert x fv) sub b
  TyBuiltin{}      -> ty
  TyIFix _ a b     -> TyIFix () (substEscape fv sub a) (substEscape fv sub b)

-- CODE REVIEW: does this exist anywhere?
renameType :: TyName -> TyName -> Type TyName DefaultUni () -> Type TyName DefaultUni ()
renameType x y | x == y    = id
               | otherwise = substType (Map.singleton x (TyVar () y))

substType :: HasCallStack
          => Map TyName (Type TyName DefaultUni ())
          -> Type TyName DefaultUni ()
          -> Type TyName DefaultUni ()
substType = substType' True

-- | Generalized substitution algorithm
substType' :: HasCallStack
           => Bool
           -- ^ Nested (True) or parallel (False)
           -> Map TyName (Type TyName DefaultUni ())
           -> Type TyName DefaultUni ()
           -> Type TyName DefaultUni ()
substType' nested sub ty0 = go fvs Set.empty sub ty0
  where
    fvs = Set.unions $ Map.keysSet sub : map ftvTy (Map.elems sub)

    go :: HasCallStack => _
    go fvs seen sub ty = case ty of
      TyVar _ x | Set.member x seen -> error "substType' loop"
      -- In the case where we do nested substitution we just continue, in parallel substitution
      -- we never go below a substitution.
      TyVar _ x | nested    -> maybe ty (go fvs (Set.insert x seen) sub) $ Map.lookup x sub
                | otherwise -> maybe ty id $ Map.lookup x sub
      TyFun _ a b      -> TyFun () (go fvs seen sub a) (go fvs seen sub b)
      TyApp _ a b      -> TyApp () (go fvs seen sub a) (go fvs seen sub b)
      TyLam _ x k b
        | Set.member x fvs -> TyLam () x' k $ go (Set.insert x' fvs) seen sub (renameType x x' b)
        | otherwise        -> TyLam () x  k $ go (Set.insert x fvs) (Set.delete x seen) sub b
        where x' = freshenTyName (fvs <> ftvTy b) x
      TyForall _ x k b
        | Set.member x fvs -> TyForall () x' k $ go (Set.insert x' fvs) seen sub (renameType x x' b)
        | otherwise        -> TyForall () x  k $ go (Set.insert x fvs) (Set.delete x seen) sub b
        where x' = freshenTyName (fvs <> ftvTy b) x
      TyBuiltin{}      -> ty
      TyIFix _ a b     -> TyIFix () (go fvs seen sub a) (go fvs seen sub b)

-- | Find all free type variables of type `a` given substitution `sub`. If variable `x` is
-- free in `a` but in the domain of `sub` we look up `x` in `sub` and get all the free type
-- variables of the result - up to the substitution.
fvTypeR :: Map TyName (Type TyName DefaultUni ()) -> Type TyName DefaultUni () -> Set TyName
fvTypeR sub a = Set.unions $ freeAndNotInSub : map (fvTypeR sub . (Map.!) sub) (Set.toList freeButInSub)
      where
          fvs = ftvTy a
          subDom = Map.keysSet sub
          freeButInSub = Set.intersection subDom fvs
          freeAndNotInSub = Set.difference fvs subDom

-- * Generators for substitutions

-- | Generate a type substitution that is valid in a given context.
genSubst :: Map TyName (Kind ()) -> Gen (Map TyName (Type TyName DefaultUni ()))
genSubst ctx = do
  xks <- sublistOf <=< shuffle $ Map.toList ctx
  go ctx Map.empty xks
  where
    go _ _ [] = return mempty
    go ctx counts ((x, k) : xs) = do
      let ctx' = Map.delete x ctx
          w    = fromMaybe 1 $ Map.lookup x counts
      ty <- sized $ \ n -> resize (div n w) $ genTypeWithCtx ctx' k
      let moreCounts = fmap (* w) $ fvTypeBag ty
          counts'    = Map.unionWith (+) counts moreCounts
      Map.insert x ty <$> go ctx' counts' xs


shrinkSubst :: Map TyName (Kind ())
            -> Map TyName (Type TyName DefaultUni ())
            -> [Map TyName (Type TyName DefaultUni ())]
shrinkSubst ctx = map Map.fromList . liftShrink shrinkTy . Map.toList
  where
    shrinkTy (x, ty) = (,) x <$> shrinkTypeAtKind (pruneCtx ctx ty) k ty
      where k = fromMaybe (error $ "internal error: " ++ show x ++ " not found") $ Map.lookup x ctx
    pruneCtx ctx ty = Map.filterWithKey (\ x _ -> Set.member x fvs) ctx
      where fvs = ftvTy ty
