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


module PlutusCore.Generators.PIR.GenTm
  ( module PlutusCore.Generators.PIR.GenTm
  , module Export
  , Arbitrary (..)
  , Gen
  ) where

import Control.Monad.Except
import Control.Monad.Reader

import Data.List.NonEmpty (NonEmpty (..))
import Data.Map (Map)
import Data.Map qualified as Map
import Data.Set (Set)
import Data.Set qualified as Set
import Data.Set.Lens (setOf)
import Data.String
import Test.QuickCheck (Arbitrary (..), Gen)
import Test.QuickCheck qualified as QC
import Test.QuickCheck.GenT as Export hiding (var)

import PlutusCore.Default
import PlutusCore.Name
import PlutusIR
import PlutusIR.Compiler
import PlutusIR.Subst

instance MonadReader r m => MonadReader r (GenT m) where
    ask = lift ask
    local f (GenT k) = GenT $ \qc size -> local f $ k qc size

-- | Term generators carry around a context to know
-- e.g. what types and terms are in scope.
type GenTm = GenT (Reader GenEnv)

data GenEnv = GenEnv
  { geSize               :: Int
  -- ^ Generator size bound. See Note [Recursion Control and geSize]
  , geDatas              :: Map TyName (Datatype TyName Name DefaultUni DefaultFun ())
  -- ^ Datatype context
  , geTypes              :: Map TyName (Kind ())
  -- ^ Type context
  , geTerms              :: Map Name (Type TyName DefaultUni ())
  -- ^ Term context
  , geUnboundUsedTyNames :: Set TyName
  -- ^ Names that we have generated and don't want to shadow but haven't bound yet.
  , geEscaping           :: AllowEscape
  -- ^ Are we in a place where we are allowed to generate a datatype binding?
  , geCustomGen          :: Maybe (Type TyName DefaultUni ())
                         -- TODO: this could return a `Maybe` perhaps. Or it
                         -- could be `Maybe (Maybe Type -> ...)`.
                         -> GenTm (Type TyName DefaultUni (), Term TyName Name DefaultUni DefaultFun ())
  -- ^ A custom user-controlled generator for terms - useful for situations where
  -- we want to e.g. generate custom strings for coverage or test some specific
  -- pattern that generates a special case for the compiler.
  , geCustomFreq         :: Int
  -- ^ How often do we use the custom generator -
  -- values in the range of 10-30 are usually reasonable.
  , geDebug              :: Bool
  -- ^ Are we currently running in debug-mode (to debug our generators)
  }

{- Note [Recursion Control and geSize]
   One would be forgiven for thinking that you don't need `geSize` in `GenTm` because
   size is built-in to `Gen`. However, if you use `Gen`s built-in size to control the size
   of both the terms you generate *and* the size of the constants in the terms you will end
   up with skewed terms. Constants near the top of the term will be big and constants near
   the bottom of the term will be small. For this reason we follow QuickCheck best practise
   and keep track of the "recursion control size" separately from `Gen`s size in the `geSize`
   field of the `GenEnv` environment.
-}

-- | Run a generator in debug-mode.
withDebug :: GenTm a -> GenTm a
withDebug gen = local (\env -> env { geDebug = True }) gen

-- | Run a `GenTm  generator in a top-level empty context where we are allowed to generate
-- datatypes.
runGenTm :: GenTm a -> Gen a
runGenTm = runGenTmCustom 0 (error "No custom generator.")

-- | Run a `GenTm` generator with a plug-in custom generator for terms that is included with
-- the other generators.
runGenTmCustom :: Int
               -> (Maybe (Type TyName DefaultUni ())
                  -> GenTm (Type TyName DefaultUni (), Term TyName Name DefaultUni DefaultFun ()))
               -> GenTm a
               -> Gen a
runGenTmCustom f cg g = do
  sized $ \ n -> do
    let env = GenEnv
          { geSize               = n
          , geDatas              = Map.empty
          , geTypes              = Map.empty
          , geTerms              = Map.empty
          , geUnboundUsedTyNames = Set.empty
          , geEscaping           = YesEscape
          , geCustomGen          = cg
          , geCustomFreq         = f
          , geDebug              = False
          }
    flip runReader env <$> runGenT g

-- * Utility functions

-- | Don't allow types to escape from a generator.
withNoEscape :: GenTm a -> GenTm a
withNoEscape = local $ \env -> env { geEscaping = NoEscape }

-- * Dealing with size

-- | Map a function over the generator size
onSize :: (Int -> Int) -> GenTm a -> GenTm a
onSize f = local $ \ env -> env { geSize = f (geSize env) }

-- | Default to the first generator if the size is zero (or negative),
-- use the second generator otherwise.
ifSizeZero :: GenTm a -> GenTm a -> GenTm a
ifSizeZero ifZ nonZ = do
  n <- asks geSize
  if n <= 0 then ifZ else nonZ

-- | Locally set the size in a generator
withSize :: Int -> GenTm a -> GenTm a
withSize = onSize . const

-- | Split the size between two generators in the ratio specified by
-- the first two arguments.
sizeSplit_ :: Int -> Int -> GenTm a -> GenTm b -> GenTm (a, b)
sizeSplit_ a b ga gb = sizeSplit a b ga (const gb)

-- | Split the size between two generators in the ratio specified by
-- the first two arguments and use the result of the first generator
-- in the second.
sizeSplit :: Int -> Int -> GenTm a -> (a -> GenTm b) -> GenTm (a, b)
sizeSplit a b ga gb = do
  n <- asks geSize
  let na = (a * n) `div` (a + b)
      nb = (b * n) `div` (a + b)
  x <- withSize na ga
  (,) x <$> withSize nb (gb x)

-- * Names

-- | Get all uniques we have generated and are used in the current context.
getUniques :: GenTm (Set Unique)
getUniques = do
  GenEnv{geDatas = dts, geTypes = tys, geTerms = tms, geUnboundUsedTyNames = used} <- ask
  return $ Set.mapMonotonic (_nameUnique . unTyName) (Map.keysSet dts <> Map.keysSet tys <> used) <>
           Set.mapMonotonic _nameUnique (Map.keysSet tms) <>
           Set.unions [ names d | d <- Map.elems dts ]
  where
    names (Datatype _ _ _ m cs) = Set.fromList $ _nameUnique m : [ _nameUnique c | VarDecl _ c _ <- cs ]

{- Note [Warning about generating fresh names]: because `GenTm` is a *reader* monad
   names are not immediately put into any state when generated. There is *no guarantee*
   that in this situation:
   ```
   do nms <- genFreshNames ss
      nms' <- genFreshNames ss
   ```
   the names in `nms` and `nms'` don't overlap.

   Instead, what you are supposed to do is locally use the names in `nms` and `nms'` to
   define generators that use them. This is done with functions like `bindTyName` and `bindTmName`:
   ```
   genLam ma mb = do
      x <- genFreshName "x"
      sizeSplit 1 7 (maybe (genType Star) return ma)
                    --      v--- LOOK HERE!
                    (\ a -> bindTmName x a . withNoEscape $ genTerm mb) $ \ a (b, body) ->
                    --      ^--- LOOK HERE!
                    TyFun () a b, LamAbs () x a body)
   ```
-}

-- | Generate a fresh name. See Note [Warning about generating fresh names].
genFreshName :: String -> GenTm Name
genFreshName s = head <$> genFreshNames [s]

-- | Generate one fresh name per string in the input list.
-- names don't overlap. See Note [Warning about generating fresh names].
genFreshNames :: [String] -> GenTm [Name]
genFreshNames ss = do
  used <- getUniques
  let i = fromEnum $ Set.findMax $ Set.insert (Unique 0) used
      js = [ j | j <- [1..i], not $ Unique j `Set.member` used ]
      is = js ++ take (length ss + 10) [i+1..]
  is' <- liftGen $ QC.shuffle is
  return [Name (fromString $ s ++ show j) (toEnum j) | (s, j) <- zip ss is']

-- | See `genFreshName`
genFreshTyName :: String -> GenTm TyName
genFreshTyName s = TyName <$> genFreshName s

-- | See `genFreshNames`
genFreshTyNames :: [String] -> GenTm [TyName]
genFreshTyNames ss = map TyName <$> genFreshNames ss

-- | Generate a name that overlaps with existing names on purpose. If there
-- are no existing names, generate a fresh name.
genNotFreshName :: String -> GenTm Name
genNotFreshName s = do
  used <- Set.toList <$> getUniques
  case used of
    [] -> genFreshName s
    _  -> liftGen $ elements [ Name (fromString $ s ++ show (unUnique i)) i | i <- used ]

-- | Generate a fresh name most (a bit more than 75%) of the time and otherwise
-- generate an already bound name. When there are no bound names generate a fresh name.
genMaybeFreshName :: String -> GenTm Name
genMaybeFreshName s = frequency [(3, genFreshName s), (1, genNotFreshName s)]

-- | See `genMaybeFreshName`
genMaybeFreshTyName :: String -> GenTm TyName
genMaybeFreshTyName s = TyName <$> genMaybeFreshName s

-- | Bind a type name to a kind and avoid capturing free type variables.
bindTyName :: TyName -> Kind () -> GenTm a -> GenTm a
bindTyName x k = local $ \ e -> e
    { geTypes = Map.insert x k (geTypes e)
    , geTerms = Map.filter (\ty -> not $ x `Set.member` setOf ftvTy ty) (geTerms e)
    , geDatas = Map.delete x (geDatas e)
    }

-- | Bind type names
bindTyNames :: [(TyName, Kind ())] -> GenTm a -> GenTm a
bindTyNames = flip $ foldr (uncurry bindTyName)

-- | Remember that we have generated a type name locally but don't bind it.
-- Useful for non-recursive definitions where we want to control name overlap.
registerTyName :: TyName -> GenTm a -> GenTm a
registerTyName n = local $ \ e -> e { geUnboundUsedTyNames = Set.insert n (geUnboundUsedTyNames e) }

-- | Bind a term to a type in a generator.
bindTmName :: Name -> Type TyName DefaultUni () -> GenTm a -> GenTm a
bindTmName x ty = local $ \ e -> e { geTerms = Map.insert x ty (geTerms e) }

-- | Bind term names
bindTmNames :: [(Name, Type TyName DefaultUni ())] -> GenTm a -> GenTm a
bindTmNames = flip $ foldr (uncurry bindTmName)

-- | Create a fresh term name, bind it to a type, and use it in a generator.
bindFreshTmName :: String -> Type TyName DefaultUni () -> (Name -> GenTm a) -> GenTm a
bindFreshTmName name ty k = do
  x <- genFreshName name
  bindTmName x ty (k x)

-- * Containers (zipper-ish, very useful for shrinking.)

-- | A type is a container for the purposes of shrinking if it has:
class Container f where
  data OneHoleContext f :: * -> *
  -- ^ One hole context where we can shrink a single "element" of the container
  oneHoleContexts :: f a -> [(OneHoleContext f a, a)]
  -- ^ A way of getting all the one hole contexts of an `f a`
  plugHole :: OneHoleContext f a -> a -> f a
  -- ^ A way to plug the hole with a new, shrunk, term

-- | Containers for lists is zipper like, a hole is a specific position in the list
instance Container [] where
  data OneHoleContext [] a = ListContext [a] [a]
  oneHoleContexts (x : xs) = (ListContext [] xs, x) : [ (ListContext (x : ys) zs, y)
                                                      | (ListContext ys zs, y) <- oneHoleContexts xs ]
  oneHoleContexts []       = []
  plugHole (ListContext xs ys) z = xs ++ [z] ++ ys

-- | An analogous implementation of `Container` as for lists
instance Container NonEmpty where
  data OneHoleContext NonEmpty a = NonEmptyContext [a] [a]
  oneHoleContexts (x :| xs) = (NonEmptyContext [] xs, x) : [ (NonEmptyContext (x : ys) zs, y)
                                                           | (ListContext ys zs, y) <- oneHoleContexts xs ]
  plugHole (NonEmptyContext []       ys) z = z :| ys
  plugHole (NonEmptyContext (x : xs) ys) z = x :| xs ++ [z] ++ ys
