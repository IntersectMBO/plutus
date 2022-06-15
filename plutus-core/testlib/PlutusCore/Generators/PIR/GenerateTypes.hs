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
import Data.Set qualified as Set
import Data.String
import GHC.Stack
import Test.QuickCheck

import PlutusCore.Builtin
import PlutusCore.Default
import PlutusCore.Generators.PIR.Common
import PlutusCore.Name
import PlutusCore.Normalize
import PlutusCore.Quote (runQuoteT)
import PlutusCore.TypeCheck.Internal (inferKindM, runTypeCheckM, withTyVar)
import PlutusIR
import PlutusIR.Error
import PlutusIR.Subst

import PlutusCore.Generators.PIR.GenTm

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

{- Note [Avoiding Shrinking Loops]

   Shrinking loops can be tricky to deal with and unfortunately there is no
   golden rule for how to avoid them. However, one good strategy to avoid them
   is to make sure shrinking isn't doing anything too clever. As a general set of
   rules:
   * Don't do "special case" shrinking that trades off size in one subterm for size
     in a different subterm. For example, it's generally dangerous to shrink
     `Node (Node Leaf (Node Leaf Leaf)) (Node Leaf Leaf)` to
     `Node Leaf (Node Leaf (Node Leaf Leaf))` even though the number of leaves is
     decreasing unless you've explicitly made "the number of leaves decreases" the
     measure by which you're shrinking (in which case you need to have a property for
     this!)
   * Carefully guard base cases - the shrinker
     `shrink tree = Leaf : someCleverShrinkingStrategy` will loop, while
     `shrink tree = [ Leaf | tree /= Leaf ] ++ someCleverShrinkingStrategy` will not.
     You will see this kind of thing used below wherever we use `minimalType` and `mkHelp`
     in the shrinkers.
   * Write properties to test your shrinkers and *run them when you change your shrinkers*.
     See e.g. `prop_noTermShrinkLoops` in module `GeneratorSpec`.
-}

-- | Give a unique "least" (intentionally vaguely specified by "shrinking order")
-- type of that kind. Note: this function requires care and attention to not get
-- a shrinking loop. If you think you need to mess with this function:
-- 0. First, you *must* read the note Note [Avoiding Shrinking Loops]
-- 1. You're probably wrong, think again and
-- 2. If you're sure you're not wrong you need to be very careful and
--    test the shrinking to make sure you don't get in a loop.
-- 3. Finally, you *must* read the note Note [Avoiding Shrinking Loops]
minimalType :: Kind () -> Type TyName DefaultUni ()
minimalType ty =
  case ty of
    Type{} -> unit
    KindArrow _ k1 k2 ->
      case k1 : view k2 of
        [Type{}]         -> list
        [Type{}, Type{}] -> pair
        _                -> TyLam () (TyName $ Name "_" (toEnum 0)) k1 $ minimalType k2
  where
    view (KindArrow _ k1 k2) = k1 : view k2
    view _                   = []

    unit = TyBuiltin () (SomeTypeIn DefaultUniUnit)
    list = TyBuiltin () (SomeTypeIn DefaultUniProtoList)
    pair = TyBuiltin () (SomeTypeIn DefaultUniProtoPair)

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
  oneofTm $ map pure (atoms ++ builtins) ++ [lam k1 k2 | KindArrow _ k1 k2 <- [k]]

-- | Generate a type at a given kind
genType :: Kind () -> GenTm (Type TyName DefaultUni ())
genType k = onSize (min 10) $
  ifSizeZero (genAtomicType k) $
    frequencyTm $ [ (1, genAtomicType k) ] ++
                  [ (2, genFun) | k == Star ] ++
                  [ (1, genForall) | k == Star ] ++
                  [ (1, genLam k1 k2) | KindArrow _ k1 k2 <- [k] ] ++
                  [ (1, genApp) ]
  where
    -- this size split keeps us from generating riddiculous types that
    -- grow huge to the left of an arrow or abstraction (See also the
    -- genApp case below). This ratio of 1:7 was not scientifically
    -- established, if you are unhappy about the compleixty of the
    -- type of arguments that are generated tweaking this might
    -- be a good idea.
    genFun = sizeSplit_ 1 7 (genType k) (genType k) (TyFun ())

    genForall = do
      x <- genMaybeFreshTyName "a"
      k <- liftGen arbitrary
      fmap (TyForall () x k) $ onSize (subtract 1) $ bindTyName x k $ genType Star

    genLam k1 k2 = do
        x <- genMaybeFreshTyName "a"
        fmap (TyLam () x k1) $ onSize (subtract 1) $ bindTyName x k1 (genType k2)

    genApp = do
      k' <- liftGen arbitrary
      sizeSplit_ 1 7 (genType $ KindArrow () k' k) (genType k') $ TyApp ()

-- | Generate a closed type at a given kind
genClosedType_ :: Kind () -> Gen (Type TyName DefaultUni ())
genClosedType_ = genTypeWithCtx mempty

-- | Generate a type in the given context with the given kind.
genTypeWithCtx :: Map TyName (Kind ()) -> Kind () -> Gen (Type TyName DefaultUni ())
genTypeWithCtx ctx k = runGenTm $ local (\ e -> e { geTypes = ctx }) (genType k)

-- | Generate a well-kinded type and its kind in a given context
genKindAndTypeWithCtx :: Map TyName (Kind ()) -> Gen (Kind(), Type TyName DefaultUni ())
genKindAndTypeWithCtx ctx = do
  k <- arbitrary
  runGenTm $ local (\ e -> e { geTypes = ctx }) ((k,) <$> genType k)

-- CODE REVIEW: does this exist anywhere??
-- | `substClosedType x sub ty` substitutes the closed type `sub` for `x` in `ty`
substClosedType :: TyName -> Type TyName DefaultUni () -> Type TyName DefaultUni () -> Type TyName DefaultUni ()
substClosedType x sub ty =
  case ty of
    TyVar _ y
      | x == y    -> sub
      | otherwise -> ty
    TyFun _ a b   -> TyFun () (substClosedType x sub a) (substClosedType x sub b)
    TyApp _ a b   -> TyApp () (substClosedType x sub a) (substClosedType x sub b)
    TyLam _ y k b
      | x == y    -> ty
      | otherwise -> TyLam () y k $ substClosedType x sub b
    TyForall _ y k b
      | x == y    -> ty
      | otherwise -> TyForall () y k $ substClosedType x sub b
    TyBuiltin{}   -> ty
    TyIFix{}      -> ty

-- | Get the kind of a builtin
builtinKind :: SomeTypeIn DefaultUni -> Kind ()
builtinKind (SomeTypeIn t) = kindOfBuiltinType t

-- * Shrinking types and kinds

-- | Shriking-order on kinds
leKind :: Kind () -> Kind () -> Bool
leKind k1 k2 = go (reverse $ args k1) (reverse $ args k2)
  where
    args Type{}            = []
    args (KindArrow _ a b) = a : args b

    go [] _                = True
    go _ []                = False
    go (k : ks) (k' : ks')
      | leKind k k' = go ks ks'
      | otherwise   = go (k : ks) ks'

-- | Strict shrinking order on kinds
ltKind :: Kind () -> Kind () -> Bool
ltKind k k' = k /= k' && leKind k k'

-- | Take a type in a context and a new target kind
--   Precondition: new kind is smaller or equal to old kind of the type.
--   TODO (later): also allow changing which context it's valid in
fixKind :: HasCallStack
        => Map TyName (Kind ())
        -> Type TyName DefaultUni ()
        -> Kind ()
        -> Type TyName DefaultUni ()
fixKind ctx ty k
  -- Nothing to do if we already have the right kind
  | unsafeInferKind ctx ty == k = ty
  | not $ k `leKind` unsafeInferKind ctx ty =
      error "fixKind not smaller"
  | otherwise = case ty of
    -- Switch a variable out for a different variable of the right kind
    TyVar _ _ | y : _ <- [ y | (y, k') <- Map.toList ctx
                             , k == k' ] -> TyVar () y
              | otherwise -> minimalType k
    -- Try to fix application by fixing the function
    TyApp _ a b       -> TyApp () (fixKind ctx a $ KindArrow () (unsafeInferKind ctx b) k) b
    TyLam _ x kx b    ->
      case k of
        -- Fix lambdas to * by substituting a minimal type for the argument
        -- and fixing the body.
        Type{}        -> fixKind ctx (substClosedType x (minimalType kx) b) k
        -- Fix functions by either keeping the argument around (if we can) or getting
        -- rid of the argument (by turning its use-sites into minimal types) and introducing
        -- a new argument.
        KindArrow _ ka kb
          | ka == kx              -> TyLam () x kx $ fixKind (Map.insert x kx ctx) b kb
          | not $ kb `leKind` kb' -> error "fixKind"
          | otherwise             -> TyLam () x ka $ fixKind ctx' b' kb
            where
              ctx' = Map.insert x ka ctx
              b'   = substClosedType x (minimalType kx) b
              kb'  = unsafeInferKind ctx' b'
    -- Ill-kinded builtins just go to minimal types
    TyBuiltin{}       -> minimalType k
    _                 -> error "fixKind"

-- | Shrink a well-kinded type in a context to new types, possibly with new kinds.
-- The new kinds are guaranteed to be smaller than or equal to the old kind.
-- TODO: also shrink to new context
--       need old context and new context
shrinkKindAndType :: HasCallStack
                  => Map TyName (Kind ())
                  -> (Kind (), Type TyName DefaultUni ())
                  -> [(Kind (), Type TyName DefaultUni ())]
shrinkKindAndType ctx (k, ty) =
  -- If we are not already minimal, add the minial type as a possible shrink.
  [(k, m) | k <- k : shrink k, m <- [minimalType k], m /= ty] ++
  -- TODO: it might be worth-while to refactor this to the structural + nonstructural
  -- style we use below. Unsure if that's more readable. CODE REVIEW: what do you think?
  case ty of
    -- Variables shrink to arbitrary "smaller" variables
    -- Note: the order on variable names here doesn't matter,
    -- it's just because we need *some* order or otherwise
    -- shrinking doesn't terminate.
    TyVar _ x         -> [ (ky, TyVar () y)
                         | (y, ky) <- Map.toList ctx
                         , ltKind ky k || ky == k && y < x]
    -- Functions shrink to either side of the arrow and both sides
    -- of the arrow shrink independently.
    TyFun _ a b       -> [(k, a), (k, b)] ++
                         [(k, TyFun () a b) | (_, a) <- shrinkKindAndType ctx (k, a)] ++
                         [(k, TyFun () a b) | (_, b) <- shrinkKindAndType ctx (k, b)]
    -- This case needs to be handled with a bit of care. First we shrink applications by
    -- doing simple stuff like shrinking the function and body separately when we can.
    -- The slightly tricky case is the concat trace. See comment below.
    TyApp _ f a       -> [(ka, a) | ka `leKind` k] ++
                         [(k, b)                     | TyLam _ x _ b <- [f], not $ Set.member x (ftvTy b)] ++
                         [(k, substClosedType x a b) | TyLam _ x _ b <- [f], null (ftvTy a)] ++
                         -- Here we try to shrink the function f, if we get something whose kind
                         -- is small enough we can return the new function f', otherwise we
                         -- apply f' to `fixKind ctx a ka'` - which takes `a` and tries to rewrite it
                         -- to something of kind `ka'`.
                         concat [case kf' of
                                   Type{}              -> [(kf', f')]
                                   KindArrow _ ka' kb' -> [ (kb', TyApp () f' (fixKind ctx a ka'))
                                                          | leKind kb' k, leKind ka' ka]
                                 | (kf', f') <- shrinkKindAndType ctx (KindArrow () ka k, f)] ++
                         -- Here we shrink the argument and fixup the function to have the right kind.
                         [(k, TyApp () (fixKind ctx f (KindArrow () ka' k)) a)
                         | (ka', a) <- shrinkKindAndType ctx (ka, a)]
      where ka = unsafeInferKind ctx a
    -- type lambdas shrink by either shrinking the kind of the argument or shrinking the body
    TyLam _ x ka b    -> [ (KindArrow () ka' kb, TyLam () x ka' $ substClosedType x (minimalType ka) b)
                         | ka' <- shrink ka] ++
                         [ (KindArrow () ka kb', TyLam () x ka b)
                         | (kb', b) <- shrinkKindAndType (Map.insert x ka ctx) (kb, b)]
      where KindArrow _ _ kb = k
    TyForall _ x ka b -> [ (k, b) | not $ Set.member x (ftvTy b) ] ++
                         -- (above) If the bound variable doesn't matter we get rid of the binding
                         [ (k, TyForall () x ka' $ substClosedType x (minimalType ka) b)
                         | ka' <- shrink ka] ++
                         -- (above) we can always just shrink the bound variable to a smaller kind
                         -- and ignore it
                         [ (k, TyForall () x ka b)
                         | (_, b) <- shrinkKindAndType (Map.insert x ka ctx) (Star, b)]
                         -- (above) or we shrink the body
    TyBuiltin{}       -> []
    TyIFix{}          -> error "shrinkKindAndType: TyIFix"

-- | Infer the kind of a type in a given kind context
inferKind :: Map TyName (Kind ()) -> Type TyName DefaultUni () -> Maybe (Kind ())
inferKind ctx ty = case runTypeCheckM () $
                          foldr (uncurry withTyVar)
                                (inferKindM @(Error DefaultUni DefaultFun ()) ty)
                                (Map.toList ctx) of
                      Left _  -> Nothing
                      Right k -> Just k

-- | Partial unsafeInferKind, useful for context where invariants are set up to guarantee
-- that types are well-kinded.
unsafeInferKind :: HasCallStack => Map TyName (Kind ()) -> Type TyName DefaultUni () -> Kind ()
unsafeInferKind ctx ty =
  case inferKind ctx ty of
    Nothing -> error "inferKind"
    Just k  -> k

-- | Shrink a type in a context assuming that it is of kind *.
shrinkType :: HasCallStack
           => Map TyName (Kind ())
           -> Type TyName DefaultUni ()
           -> [Type TyName DefaultUni ()]
shrinkType ctx ty = map snd $ shrinkKindAndType ctx (Star, ty)

-- | Shrink a type of a given kind in a given context in a way that keeps its kind
shrinkTypeAtKind :: HasCallStack
                 => Map TyName (Kind ())
                 -> Kind ()
                 -> Type TyName DefaultUni ()
                 -> [Type TyName DefaultUni ()]
shrinkTypeAtKind ctx k ty = [ ty' | (k', ty') <- shrinkKindAndType ctx (k, ty), k == k' ]

-- | Check well-kindedness of a type in a context
checkKind :: Map TyName (Kind ()) -> Type TyName DefaultUni () -> Kind () -> Bool
checkKind ctx ty k = inferKind ctx ty == Just k

-- | Generate an arbitrary kind and closed type of that kind.
genKindAndType :: Gen (Kind (), Type TyName DefaultUni ())
genKindAndType = do
  k <- arbitrary
  t <- genClosedType_ k
  return (k, t)

-- | Normalize a type, throw an error if normalization fails due to e.g. wellkindedness issues.
normalizeTy :: Type TyName DefaultUni () -> Type TyName DefaultUni ()
normalizeTy ty = case runQuoteT $ normalizeType ty of
  Left _                 -> error "normalizeTy"
  Right (Normalized ty') -> ty'

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

-- CODE REVIEW: this should probably go somewhere else (??), where? Does it already exist?!
instance Arbitrary (Kind ()) where
  arbitrary = sized $ arb . (`div` 3)
    where
      arb 0 = pure $ Star
      arb n = frequency [(4, pure $ Star),
                         (1, (:->) <$> arb (div n 6) <*> arb (div (5 * n) 6))]
  shrink Star      = []
  shrink (a :-> b) = [b] ++ [a' :-> b' | (a', b') <- shrink (a, b)]
    -- Note: `a` can have bigger arity than `a -> b` so don't shrink to it!
