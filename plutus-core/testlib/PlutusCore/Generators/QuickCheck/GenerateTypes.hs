{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TupleSections #-}

module PlutusCore.Generators.QuickCheck.GenerateTypes where

import PlutusCore.Generators.QuickCheck.Builtin
import PlutusCore.Generators.QuickCheck.Common
import PlutusCore.Generators.QuickCheck.GenTm
import PlutusCore.Generators.QuickCheck.GenerateKinds ()

import PlutusCore.Builtin
import PlutusCore.Core
import PlutusCore.Default
import PlutusCore.Name.Unique
import PlutusCore.Normalize
import PlutusCore.Pretty
import PlutusCore.Quote (runQuote)
import PlutusIR

import Control.Monad (replicateM, when)
import Control.Monad.Reader (asks, local)
import Data.Foldable
import Data.Map.Strict qualified as Map
import Data.Maybe
import Data.String
import Test.QuickCheck (chooseInt, shuffle)

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

{-| Generate "small" types at a given kind such as builtins, bound variables, bound datatypes,
and lambda abstractions \ t0 ... tn. T -}
genAtomicType :: Kind () -> GenTm (Type TyName DefaultUni ())
genAtomicType k = do
  tys <- asks geTypes
  dts <- asks geDatas
  let atoms =
        [TyVar () x | (x, k') <- Map.toList tys, k == k']
          ++ [TyVar () x | (x, Datatype _ (TyVarDecl _ _ k') _ _ _) <- Map.toList dts, k == k']
      genBuiltin = fmap (TyBuiltin ()) <$> genBuiltinTypeOf k
      lam k1 k2 = do
        x <- genMaybeFreshTyName "a"
        TyLam () x k1 <$> bindTyName x k1 (genAtomicType k2)
  -- There's always an atomic type of a given kind, hence the usage of 'deliver': we definitely have
  -- builtin types of kind @*@, and for all other kinds we can generate type lambdas.
  deliver $
    frequency
      [ (7, if null atoms then pure Nothing else Just <$> elements atoms)
      , (1, liftGen genBuiltin)
      , -- There may not be a type variable or a built-in type of the given type, hence we have to
        -- resort to generating a lambda occasionally. Plus it's a lambda that ignores the bound
        -- variable in its body, so it's fine to call it "atomic".
        (3, sequence $ listToMaybe [lam k1 k2 | KindArrow _ k1 k2 <- [k]])
      ]

-- | Generate a type at a given kind
genType :: Kind () -> GenTm (Type TyName DefaultUni ())
genType k = do
  ty <-
    onAstSize (min 10) $
      ifAstSizeZero (genAtomicType k) $
        frequency $
          concat
            [ [(5, genAtomicType k)]
            , [(10, genFun) | k == Type ()]
            , [(5, genForall) | k == Type ()]
            , [(1, genIFix) | k == Type ()]
            , [(5, genLam k1 k2) | KindArrow _ k1 k2 <- [k]]
            , [(5, genApp)]
            , [(3, genSOP) | k == Type ()]
            ]
  debug <- asks geDebug
  when debug $ do
    ctx <- asks geTypes
    case checkKind ctx ty k of
      Right _ -> pure ()
      Left err ->
        error . show $
          fold
            [ "genType - checkInvariants: type " <> prettyReadable ty
            , " does not match kind " <> prettyReadable k
            , " in context " <> prettyReadable ctx
            , " with error message " <> fromString err
            ]
  pure ty
  where
    -- This size split keeps us from generating ridiculous types that
    -- grow huge to the left of an arrow or abstraction (See also the
    -- genApp case below). This ratio of 1:7 was not scientifically
    -- established, if you are unhappy about the compleixty of the
    -- type of arguments that are generated tweaking this might
    -- be a good idea.
    genFun = uncurry (TyFun ()) <$> astSizeSplit_ 1 7 (genType k) (genType k)

    genForall = do
      a <- genMaybeFreshTyName "a"
      k' <- liftGen arbitrary
      fmap (TyForall () a k') $ onAstSize (subtract 1) $ bindTyName a k' $ genType $ Type ()

    genLam k1 k2 = do
      a <- genMaybeFreshTyName "a"
      fmap (TyLam () a k1) $ onAstSize (subtract 1) $ bindTyName a k1 (genType k2)

    genApp = do
      k' <- liftGen arbitrary
      uncurry (TyApp ()) <$> astSizeSplit_ 1 7 (genType $ KindArrow () k' k) (genType k')

    genIFix = do
      k' <- liftGen arbitrary
      uncurry (TyIFix ())
        <$> astSizeSplit_
          5
          2
          (genType $ toPatFuncKind k')
          (genType k')

    genSOP = do
      n <- asks geAstSize
      -- Generate up to five constructors or fewer than that if we don't have much size left.
      iSum <- liftGen $ chooseInt (0, min 5 $ n `div` 5)
      jsProd <-
        liftGen . replicateM iSum $
          -- The more constructors a data type has, the less arguments each of them can have.
          -- This is so that we don't generate data types with a large number of constructors each
          -- which takes a large number of arguments.
          chooseInt (0, min (7 - iSum) $ n `div` (2 * iSum))
      withAstSize (n `div` sum jsProd) $
        TySOP () <$> traverse (\j -> replicateM j . genType $ Type ()) jsProd

-- | Generate a closed type at a given kind
genClosedType :: Kind () -> Gen (Type TyName DefaultUni ())
genClosedType = genTypeWithCtx mempty

-- | Generate a closed type at a given kind
genClosedTypeDebug :: Kind () -> Gen (Type TyName DefaultUni ())
genClosedTypeDebug = genTypeWithCtxDebug mempty

-- | Generate a type in the given context with the given kind.
genTypeWithCtx :: TypeCtx -> Kind () -> Gen (Type TyName DefaultUni ())
genTypeWithCtx ctx k = runGenTm $ local (\e -> e {geTypes = ctx}) (genType k)

-- | Generate a type in the given context with the given kind.
genTypeWithCtxDebug :: TypeCtx -> Kind () -> Gen (Type TyName DefaultUni ())
genTypeWithCtxDebug ctx k = runGenTm $ local (\e -> e {geTypes = ctx}) (withDebug $ genType k)

-- | Generate a well-kinded type and its kind in a given context
genKindAndTypeWithCtx :: TypeCtx -> Gen (Kind (), Type TyName DefaultUni ())
genKindAndTypeWithCtx ctx = do
  k <- arbitrary
  runGenTm $ local (\e -> e {geTypes = ctx}) ((k,) <$> genType k)

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

-- See Note [Chaotic Good fresh name generation].
-- | Generate a context of free type variables with kinds
genCtx :: Gen TypeCtx
genCtx = do
  let m = 20
  n <- choose (0, m)
  let xVars = [TyName $ Name (fromString $ "x" ++ show i) (toEnum i) | i <- [1 .. m]]
  shuf <- shuffle xVars
  let xs = take n shuf
  ks <- vectorOf n arbitrary
  return $ Map.fromList $ zip xs ks
