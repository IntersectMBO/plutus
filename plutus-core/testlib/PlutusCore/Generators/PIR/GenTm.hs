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


module PlutusCore.Generators.PIR.GenTm where

import Control.Applicative ((<|>))
import Control.Arrow hiding ((<+>))
import Control.Lens ((<&>))
import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.Trans.Maybe

import Data.Foldable
import Data.List.NonEmpty (NonEmpty (..))
import Data.Map (Map)
import Data.Map qualified as Map
import Data.Maybe
import Data.Set (Set)
import Data.Set qualified as Set
import Data.String
import GHC.Stack
import Prettyprinter
import Test.QuickCheck
import Text.PrettyBy

import PlutusCore.Default
import PlutusCore.Name
import PlutusCore.Normalize
import PlutusCore.Quote (runQuoteT)
import PlutusCore.Rename
import PlutusIR
import PlutusIR.Compiler
import PlutusIR.Core.Instance.Pretty.Readable
import PlutusIR.Error
import PlutusIR.Subst
import PlutusIR.TypeCheck

-- | Term generators carry around a context to know
-- e.g. what types and terms are in scope.
type GenTm = ReaderT GenEnv Gen

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
runGenTmCustom f cg g = sized $ \ n ->
  runReaderT g $ GenEnv { geSize               = n
                        , geDatas              = Map.empty
                        , geTypes              = Map.empty
                        , geTerms              = Map.empty
                        , geUnboundUsedTyNames = Set.empty
                        , geEscaping           = YesEscape
                        , geCustomGen          = cg
                        , geCustomFreq         = f
                        }

-- * Utility functions

-- | Don't allow types to escape from a generator.
noEscape :: GenTm a -> GenTm a
noEscape = local $ \env -> env { geEscaping = NoEscape }

-- * Functions for lifting `Gen` stuff to `GenTm`

-- | Lift `Gen` generator to `GenTm` generator. Respects `geSize`.
liftGen :: Gen a -> GenTm a
liftGen gen = do
  sz <- asks geSize
  lift $ resize sz gen

-- | Lift functor operations like `oneof` from `Gen` to `GenTm`
liftGenF :: Functor f => (f (Gen a) -> Gen a) -> f (GenTm a) -> GenTm a
liftGenF oo gs = ReaderT $ \ env -> oo $ fmap (`runReaderT` env) gs

-- | Uniformly choose one of the generators in the list. Requires the
-- list to be non-empty.
oneofTm :: [GenTm a] -> GenTm a
oneofTm = liftGenF oneof

-- | Functor of frequency-lists. Only used with `liftGenF` in `frequencyTm`
-- below. (One could have wished for Haskell to give us the ability to use this
-- functor without having to write down a newtype, but here we are).
newtype FreqList a = FreqList { unFreqList :: [(Int, a)] }
  deriving stock Functor

-- | Non-uniformly pick a generator from the list weighted by
-- the first item in the tuple.
frequencyTm :: [(Int, GenTm a)] -> GenTm a
frequencyTm = liftGenF (frequency . unFreqList) . FreqList

-- | Lift a generator from items to lists.
listTm :: GenTm a -> GenTm [a]
listTm g = do
  sz <- asks geSize
  n  <- liftGen $ choose (0, div sz 3)
  onSize (`div` n) $ replicateM n g

-- | Generate exactly `n` items of a given generator
vecTm :: Int -> GenTm a -> GenTm [a]
vecTm n = sequence . replicate n

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
sizeSplit_ :: Int -> Int -> GenTm a -> GenTm b -> (a -> b -> c) -> GenTm c
sizeSplit_ a b ga gb = sizeSplit a b ga (const gb)

-- | Split the size between two generators in the ratio specified by
-- the first two arguments and use the result of the first generator
-- in the second.
sizeSplit :: Int -> Int -> GenTm a -> (a -> GenTm b) -> (a -> b -> c) -> GenTm c
sizeSplit a b ga gb f = do
  n <- asks geSize
  let na = (a * n) `div` (a + b)
      nb = (b * n) `div` (a + b)
  x <- withSize na ga
  f x <$> withSize nb (gb x)

-- * Names

-- | Get all uniques we have generated and are used in the current context.
getUniques :: GenTm (Set Unique)
getUniques = do
  GenEnv{geDatas = dts, geTypes = tys, geTerms = tms, geUnboundUsedTyNames = used} <- ask
  return $ Set.mapMonotonic (nameUnique . unTyName) (Map.keysSet dts <> Map.keysSet tys <> used) <>
           Set.mapMonotonic nameUnique (Map.keysSet tms) <>
           Set.unions [ names d | d <- Map.elems dts ]
  where
    names (Datatype _ _ _ m cs) = Set.fromList $ nameUnique m : [ nameUnique c | VarDecl _ c _ <- cs ]

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
                    (\ a -> bindTmName x a . noEscape $ genTerm mb) $ \ a (b, body) ->
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
  is' <- liftGen $ shuffle is
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
genMaybeFreshName s = frequencyTm [(3, genFreshName s), (1, genNotFreshName s)]

-- | See `genMaybeFreshName`
genMaybeFreshTyName :: String -> GenTm TyName
genMaybeFreshTyName s = TyName <$> genMaybeFreshName s

-- | Bind a type name to a kind and avoid capturing free type variables.
bindTyName :: TyName -> Kind () -> GenTm a -> GenTm a
bindTyName x k = local $ \ e -> e { geTypes = Map.insert x k (geTypes e)
                                  , geTerms = Map.filter (\ty -> not $ x `Set.member` ftvTy ty) (geTerms e)
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
