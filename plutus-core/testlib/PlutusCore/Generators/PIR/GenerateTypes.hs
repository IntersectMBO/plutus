-- editorconfig-checker-disable-file
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
{-# OPTIONS_GHC -Wno-incomplete-uni-patterns #-}
{-# OPTIONS_GHC -Wno-partial-type-signatures #-}
{-# OPTIONS_GHC -Wno-orphans #-}
{-# OPTIONS_GHC -Wno-redundant-constraints #-}

module PlutusCore.Generators.PIR.GenerateTypes where

import Control.Monad.Reader

import Data.Map (Map)
import Data.Map qualified as Map
import Data.String
import Test.QuickCheck (shuffle)
import Test.QuickCheck.GenT

import PlutusCore.Builtin
import PlutusCore.Default
import PlutusCore.Generators.PIR.Common
import PlutusCore.Name
import PlutusCore.Normalize
import PlutusCore.Quote (runQuote)
import PlutusIR
import PlutusIR.Core.Instance.Pretty.Readable
import PlutusIR.Error

import PlutusCore.Generators.PIR.GenTm
import PlutusCore.Generators.PIR.GenerateKinds ()

{- Note [Debugging generators that don't generate well-typed/kinded terms/types]
    This module implements generators for well-typed terms and well-kinded types.
    If you came here after a property like `prop_genTypeCorrect` failed and you
    didn't get a minimal counterexample (because shrinking requries well-typed terms)
    you need to use a different trick. One trick that often works is to add the well-typedness
    check in the generators - e.g. in `genTerm` you can do something like this:
    ```
    genTerm ... = myCheck $ do
      ...
      where
        myCheck gen = do
          (trm, type) <- gen
          if notConformingToExpectedInvariant trm type then
            error (show trm ++ " " ++ show type)
          else
            return (trm, type)
    ```
-}

-- * Generators for well-kinded types

-- | Get the types of builtins at a given kind
builtinTysAt :: Kind () -> [SomeTypeIn DefaultUni]
builtinTysAt Star =
  -- TODO: add 'DefaultUniData' once it has a non-throwing 'ArbitraryBuiltin' instance.
  [ SomeTypeIn DefaultUniInteger
  , SomeTypeIn DefaultUniUnit
  , SomeTypeIn DefaultUniBool
  , SomeTypeIn DefaultUniByteString
  , SomeTypeIn DefaultUniString
  -- TODO: should we have more examples of lists and pairs here?
  , SomeTypeIn $ DefaultUniList DefaultUniBool
  , SomeTypeIn $ DefaultUniPair DefaultUniInteger DefaultUniUnit]
builtinTysAt (Star :-> Star) =
  [ SomeTypeIn DefaultUniProtoList
  , SomeTypeIn $ DefaultUniProtoPair `DefaultUniApply` DefaultUniString
  ]
builtinTysAt (Star :-> Star :-> Star) = [SomeTypeIn DefaultUniProtoPair]
builtinTysAt _ = []

-- | Generate "small" types at a given kind such as builtins, bound variables, bound datatypes,
-- and lambda abstractions \ t0 ... tn. T
genAtomicType :: Kind () -> GenTm (Type TyName DefaultUni ())
genAtomicType k = do
  tys <- asks geTypes
  dts <- asks geDatas
  let atoms = [ TyVar () x | (x, k') <- Map.toList tys, k == k' ] ++
              [ TyVar () x | (x, Datatype _ (TyVarDecl _ _ k') _ _ _) <- Map.toList dts, k == k' ]
      builtins = map (TyBuiltin ()) $ builtinTysAt k
      lam k1 k2 = do
        x <- genMaybeFreshTyName "a"
        TyLam () x k1 <$> bindTyName x k1 (genAtomicType k2)
  -- TODO: probably should be 'frequencyTm'?
  oneof $ concat
    [ map pure atoms
    , [elements builtins | not $ null builtins]
    , [lam k1 k2 | KindArrow _ k1 k2 <- [k]]
    ]

-- | Generate a type at a given kind
genType :: Kind () -> GenTm (Type TyName DefaultUni ())
genType k = checkInvariants $ onSize (min 10) $
  ifSizeZero (genAtomicType k) $
    frequency $
      [ (5, genAtomicType k) ] ++
      [ (10, genFun) | k == Star ] ++
      [ (5, genForall) | k == Star ] ++
      [ (1, genIFix) | k == Star ] ++
      [ (5, genLam k1 k2) | KindArrow _ k1 k2 <- [k] ] ++
      [ (5, genApp) ]
  where

    checkInvariants gen = do
      ty <- gen
      debug <- asks geDebug
      ctx <- asks geTypes
      if debug then
        case checkKind ctx ty k of
          Left err ->
             (error . show $ "genType - checkInvariants: type " <> prettyPirReadable ty
                           <> " does not match kind " <> prettyPirReadable k
                           <> " in context " <> prettyPirReadable ctx
                           <> " with error message " <> fromString err)
          _ -> return ty
      else
        return ty

    -- this size split keeps us from generating riddiculous types that
    -- grow huge to the left of an arrow or abstraction (See also the
    -- genApp case below). This ratio of 1:7 was not scientifically
    -- established, if you are unhappy about the compleixty of the
    -- type of arguments that are generated tweaking this might
    -- be a good idea.
    genFun = uncurry (TyFun ()) <$> sizeSplit_ 1 7 (genType k) (genType k)

    genForall = do
      x <- genMaybeFreshTyName "a"
      k <- liftGen arbitrary
      fmap (TyForall () x k) $ onSize (subtract 1) $ bindTyName x k $ genType Star

    genLam k1 k2 = do
        x <- genMaybeFreshTyName "a"
        fmap (TyLam () x k1) $ onSize (subtract 1) $ bindTyName x k1 (genType k2)

    genApp = do
      k' <- liftGen arbitrary
      uncurry (TyApp ()) <$> sizeSplit_ 1 7 (genType $ KindArrow () k' k) (genType k')

    genIFix = do
      k' <- liftGen arbitrary
      uncurry (TyIFix ()) <$> sizeSplit_ 5 2
        (genType $ (k' :-> Star) :-> k' :-> Star)
        (genType k')

-- | Generate a closed type at a given kind
genClosedType_ :: Kind () -> Gen (Type TyName DefaultUni ())
genClosedType_ = genTypeWithCtx mempty

-- | Generate a closed type at a given kind
genClosedTypeDebug_ :: Kind () -> Gen (Type TyName DefaultUni ())
genClosedTypeDebug_ = genTypeWithCtxDebug mempty

-- | Generate a type in the given context with the given kind.
genTypeWithCtx :: Map TyName (Kind ()) -> Kind () -> Gen (Type TyName DefaultUni ())
genTypeWithCtx ctx k = runGenTm $ local (\ e -> e { geTypes = ctx }) (genType k)

-- | Generate a type in the given context with the given kind.
genTypeWithCtxDebug :: Map TyName (Kind ()) -> Kind () -> Gen (Type TyName DefaultUni ())
genTypeWithCtxDebug ctx k = runGenTm $ local (\ e -> e { geTypes = ctx }) (withDebug $ genType k)

-- | Generate a well-kinded type and its kind in a given context
genKindAndTypeWithCtx :: Map TyName (Kind ()) -> Gen (Kind(), Type TyName DefaultUni ())
genKindAndTypeWithCtx ctx = do
  k <- arbitrary
  runGenTm $ local (\ e -> e { geTypes = ctx }) ((k,) <$> genType k)

-- | Get the kind of a builtin
builtinKind :: SomeTypeIn DefaultUni -> Kind ()
builtinKind (SomeTypeIn t) = kindOfBuiltinType t

-- | Generate an arbitrary kind and closed type of that kind.
genKindAndType :: Gen (Kind (), Type TyName DefaultUni ())
genKindAndType = do
  k <- arbitrary
  t <- genClosedType_ k
  return (k, t)

-- | Generate an arbitrary kind and closed type of that kind.
genKindAndTypeDebug :: Gen (Kind (), Type TyName DefaultUni ())
genKindAndTypeDebug = do
  k <- arbitrary
  t <- genClosedTypeDebug_ k
  return (k, t)

-- | Normalize a type, throw an error if normalization fails due to e.g. wellkindedness issues.
normalizeTy :: Type TyName DefaultUni () -> Type TyName DefaultUni ()
normalizeTy = unNormalized . runQuote . normalizeType

-- | Generate a context of free type variables with kinds
genCtx :: Gen (Map TyName (Kind ()))
genCtx = do
  let m = 20
  n <- choose (0, m)
  let allTheVarsCalledX = [ TyName $ Name (fromString $ "x" ++ show i) (toEnum i) | i <- [1..m] ]
  shuf <- shuffle allTheVarsCalledX
  let xs = take n shuf
  ks <- vectorOf n arbitrary
  return $ Map.fromList $ zip xs ks
