{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TupleSections     #-}

module PlutusCore.Generators.PIR.GenerateTypes where

import Control.Monad.Reader

import Data.Map.Strict qualified as Map
import Data.String
import Test.QuickCheck (shuffle)
import Test.QuickCheck.GenT

import PlutusCore.Builtin
import PlutusCore.Core
import PlutusCore.Default
import PlutusCore.Generators.PIR.Common
import PlutusCore.Name
import PlutusCore.Normalize
import PlutusCore.Quote (runQuote)
import PlutusIR
import PlutusIR.Core.Instance.Pretty.Readable

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

-- TODO: make this a proper generator running in 'GenTm'.
-- | Get the types of builtins at a given kind
builtinTysAt :: Kind () -> [SomeTypeIn DefaultUni]
builtinTysAt (Type _) =
  -- TODO: add 'DefaultUniData' once it has a non-throwing 'ArbitraryBuiltin' instance.
  [ SomeTypeIn DefaultUniInteger
  , SomeTypeIn DefaultUniUnit
  , SomeTypeIn DefaultUniBool
  , SomeTypeIn DefaultUniByteString
  , SomeTypeIn DefaultUniString
  -- TODO: should we have more examples of lists and pairs here?
  , SomeTypeIn $ DefaultUniList DefaultUniBool
  , SomeTypeIn $ DefaultUniPair DefaultUniInteger DefaultUniUnit]
builtinTysAt (KindArrow _ (Type _) (Type _)) =
  [ SomeTypeIn DefaultUniProtoList
  , SomeTypeIn $ DefaultUniProtoPair `DefaultUniApply` DefaultUniString
  ]
builtinTysAt (KindArrow _ (Type _) (KindArrow () (Type _) (Type _))) =
  [SomeTypeIn DefaultUniProtoPair]
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
      [ (10, genFun) | k == Type () ] ++
      [ (5, genForall) | k == Type () ] ++
      [ (1, genIFix) | k == Type () ] ++
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
      k' <- liftGen arbitrary
      fmap (TyForall () x k') $ onSize (subtract 1) $ bindTyName x k' $ genType $ Type ()

    genLam k1 k2 = do
        x <- genMaybeFreshTyName "a"
        fmap (TyLam () x k1) $ onSize (subtract 1) $ bindTyName x k1 (genType k2)

    genApp = do
      k' <- liftGen arbitrary
      uncurry (TyApp ()) <$> sizeSplit_ 1 7 (genType $ KindArrow () k' k) (genType k')

    genIFix = do
      k' <- liftGen arbitrary
      uncurry (TyIFix ()) <$> sizeSplit_ 5 2
        (genType $ toPatFuncKind k')
        (genType k')

-- | Generate a closed type at a given kind
genClosedType :: Kind () -> Gen (Type TyName DefaultUni ())
genClosedType = genTypeWithCtx mempty

-- | Generate a closed type at a given kind
genClosedTypeDebug :: Kind () -> Gen (Type TyName DefaultUni ())
genClosedTypeDebug = genTypeWithCtxDebug mempty

-- | Generate a type in the given context with the given kind.
genTypeWithCtx :: TypeCtx -> Kind () -> Gen (Type TyName DefaultUni ())
genTypeWithCtx ctx k = runGenTm $ local (\ e -> e { geTypes = ctx }) (genType k)

-- | Generate a type in the given context with the given kind.
genTypeWithCtxDebug :: TypeCtx -> Kind () -> Gen (Type TyName DefaultUni ())
genTypeWithCtxDebug ctx k = runGenTm $ local (\ e -> e { geTypes = ctx }) (withDebug $ genType k)

-- | Generate a well-kinded type and its kind in a given context
genKindAndTypeWithCtx :: TypeCtx -> Gen (Kind(), Type TyName DefaultUni ())
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
  t <- genClosedType k
  return (k, t)

-- | Generate an arbitrary kind and closed type of that kind.
genKindAndTypeDebug :: Gen (Kind (), Type TyName DefaultUni ())
genKindAndTypeDebug = do
  k <- arbitrary
  t <- genClosedTypeDebug k
  return (k, t)

-- | Normalize a type.
normalizeTy :: Type TyName DefaultUni () -> Type TyName DefaultUni ()
normalizeTy = unNormalized . runQuote . normalizeType

-- | Generate a context of free type variables with kinds
genCtx :: Gen TypeCtx
genCtx = do
  let m = 20
  n <- choose (0, m)
  let allTheVarsCalledX = [ TyName $ Name (fromString $ "x" ++ show i) (toEnum i) | i <- [1..m] ]
  shuf <- shuffle allTheVarsCalledX
  let xs = take n shuf
  ks <- vectorOf n arbitrary
  return $ Map.fromList $ zip xs ks
