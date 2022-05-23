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

module PlutusCore.Generators.PIR where

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
import PlutusIR.TypeCheck

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

-- | Term generators carry around a context to know
-- e.g. what types and terms are in scope.
type GenTm = ReaderT GenEnv Gen

data GenEnv = GenEnv
  { geSize               :: Int
  -- ^ Generator size bound
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
                         -> GenTm (Type TyName DefaultUni (), Term TyName Name DefaultUni DefaultFun ())
  -- ^ A custom user-controlled generator for terms - useful for situations where
  -- we want to e.g. generate custom strings for coverage or test some specific
  -- pattern that generates a special case for the compiler.
  , geCustomFreq         :: Int
  -- ^ How often do we use the custom generator -
  -- values in the range of 10-30 are usually reasonable.
  }

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

-- * Dealing with fresh names

-- | Get the free variables of a term
fvTerm :: Term TyName Name DefaultUni DefaultFun ()
       -> Set Name
fvTerm tm = case tm of
  Let _ Rec binds body -> Set.unions
    (fvTerm body : [ fvTerm body | TermBind _ _ _ body <- toList binds ])
    `Set.difference` Map.keysSet (foldr addTmBind mempty binds)
  Let _ _ binds body -> foldr go (fvTerm body) binds
    where go (TermBind _ _ (VarDecl _ x _) body) free = fvTerm body <> Set.delete x free
          go _ free                                   = free
  Var _ nm       -> Set.singleton nm
  TyAbs _ _ _ t  -> fvTerm t
  LamAbs _ x _ t -> Set.delete x (fvTerm t)
  Apply _ t t'   -> fvTerm t <> fvTerm t'
  TyInst _ t _   -> fvTerm t
  Constant{}     -> mempty
  Builtin{}      -> mempty
  Error{}        -> mempty
  IWrap{}        -> error "fvTerm: IWrap"
  Unwrap{}       -> error "fvTerm: Unwrap"

-- | Get the free variables in a type that appear in negative position
negativeVars :: Type TyName DefaultUni () -> Set TyName
negativeVars ty = case ty of
  TyFun _ a b      -> positiveVars a <> negativeVars b
  TyApp _ a b      -> negativeVars a <> negativeVars b
  TyLam _ x _ b    -> Set.delete x $ negativeVars b
  TyForall _ x _ b -> Set.delete x $ negativeVars b
  TyVar _ _        -> mempty
  TyBuiltin{}      -> mempty
  TyIFix{}         -> error "negativeVars: TyIFix"

-- | Get the free variables in a type that appear in positive position
positiveVars :: Type TyName DefaultUni () -> Set TyName
positiveVars ty = case ty of
  TyFun _ a b      -> negativeVars a <> positiveVars b
  TyApp _ a b      -> positiveVars a <> positiveVars b
  TyLam _ x _ b    -> Set.delete x $ positiveVars b
  TyForall _ x _ b -> Set.delete x $ positiveVars b
  TyVar _ x        -> Set.singleton x
  TyBuiltin{}      -> mempty
  TyIFix{}         -> error "positiveVars: TyIFix"

-- | Get the free type variables in a type along with how many
-- times they occur. The elements of the map are guaranteed to be
-- non-zero.
fvTypeBag :: Type TyName DefaultUni () -> Map TyName Int
fvTypeBag ty = case ty of
  TyVar _ x        -> Map.singleton x 1
  TyFun _ a b      -> Map.unionWith (+) (fvTypeBag a) (fvTypeBag b)
  TyApp _ a b      -> Map.unionWith (+) (fvTypeBag a) (fvTypeBag b)
  TyLam _ x _ b    -> Map.delete x (fvTypeBag b)
  TyForall _ x _ b -> Map.delete x (fvTypeBag b)
  TyBuiltin{}      -> Map.empty
  TyIFix{}         -> error "fvTypeBag: TyIFix"

-- | Get the free type variables in a term.
fvType :: Type TyName DefaultUni () -> Set TyName
fvType = Map.keysSet . fvTypeBag

-- | Recursively find all free type variables ina a substitution
fvTypeR :: Map TyName (Type TyName DefaultUni ()) -> Type TyName DefaultUni () -> Set TyName
fvTypeR sub a = Set.unions $ ns : map (fvTypeR sub . (Map.!) sub) (Set.toList ss)
      where
          fvs = fvType a
          ss  = Set.intersection (Map.keysSet sub) fvs
          ns  = Set.difference fvs ss

-- | Get all uniques we have generated and are used in the current context.
getUniques :: GenTm (Set Unique)
getUniques = do
  GenEnv{geDatas = dts, geTypes = tys, geTerms = tms, geUnboundUsedTyNames = used} <- ask
  return $ Set.mapMonotonic (nameUnique . unTyName) (Map.keysSet dts <> Map.keysSet tys <> used) <>
           Set.mapMonotonic nameUnique (Map.keysSet tms) <>
           Set.unions [ names d | d <- Map.elems dts ]
  where
    names (Datatype _ _ _ m cs) = Set.fromList $ nameUnique m : [ nameUnique c | VarDecl _ c _ <- cs ]

-- | Freshen a TyName so that it does not equal any of the names in the set.
freshenTyName :: Set TyName -> TyName -> TyName
freshenTyName fvs (TyName (Name x j)) = TyName (Name x i)
  where i  = succ $ Set.findMax is
        is = Set.insert j $ Set.insert (toEnum 0) $ Set.mapMonotonic (nameUnique . unTyName) fvs

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
                                  , geTerms = Map.filter (\ty -> not $ x `Set.member` fvType ty) (geTerms e)
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

-- | Get the names and types of the constructors of a datatype.
constrTypes :: Datatype TyName Name DefaultUni DefaultFun () -> [(Name, Type TyName DefaultUni ())]
constrTypes (Datatype _ _ xs _ cs) = [ (c, abstr ty) | VarDecl _ c ty <- cs ]
  where
    abstr ty = foldr (\ (TyVarDecl _ x k) -> TyForall () x k) ty xs


-- | Get the name and type of the match function for a given datatype.
matchType :: Datatype TyName Name DefaultUni DefaultFun () -> (Name, (Type TyName DefaultUni ()))
matchType (Datatype _ (TyVarDecl _ a _) xs m cs) = (m, matchType)
  where
    fvs = Set.fromList (a : [x | TyVarDecl _ x _ <- xs]) <>
          mconcat [fvType ty | VarDecl _ _ ty <- cs]
    pars = [TyVar () x | TyVarDecl _ x _ <- xs]
    dtyp = foldl (TyApp ()) (TyVar () a) pars
    matchType = abstr $ dtyp ->> TyForall () r Star (foldr ((->>) . conArg) (TyVar () r) cs)
      where r = freshenTyName fvs $ TyName $ Name "r" (toEnum 0)
            conArg (VarDecl _ _ ty) = setTarget ty
            setTarget (TyFun _ a b) = TyFun () a (setTarget b)
            setTarget _             = TyVar () r
    abstr ty = foldr (\ (TyVarDecl _ x k) -> TyForall () x k) ty xs

-- | Bind a datatype declaration in a generator.
bindDat :: Datatype TyName Name DefaultUni DefaultFun ()
        -> GenTm a
        -> GenTm a
bindDat dat@(Datatype _ (TyVarDecl _ a k) _ _ _) cont =
  bindTyName a k $
  local (\ e -> e { geDatas = Map.insert a dat (geDatas e) }) $
  foldr (uncurry bindTmName) cont (matchType dat : constrTypes dat)

-- | Bind a binding.
bindBind :: Binding TyName Name DefaultUni DefaultFun ()
         -> GenTm a
         -> GenTm a
bindBind (DatatypeBind _ dat)              = bindDat dat
bindBind (TermBind _ _ (VarDecl _ x ty) _) = bindTmName x ty
-- CODE REVIEW: Should we try to generate type bindings and all the recursive types without datatypes stuff?
-- I don't think both datatypes and this stuff should actually show up in the same code, no?
bindBind _                                 = error "unreachable"

-- | Bind multiple bindings
bindBinds :: Foldable f => f (Binding TyName Name DefaultUni DefaultFun ()) -> GenTm a -> GenTm a
bindBinds = flip (foldr bindBind)

-- * Generators for well-kinded types

-- | Give a unique "least" (intentionally vaguely specified by "shrinking order")
-- type of that kind. Note: this function requires care and attention to not get
-- a shrinking loop. If you think you need to mess with this function:
-- 1. You're probably wrong, think again and
-- 2. If you're sure you're not wrong you need to be very careful and
--    test the shrinking to make sure you don't get in a loop.
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
builtinTys :: Kind () -> [SomeTypeIn DefaultUni]
builtinTys Star =
  [ SomeTypeIn DefaultUniInteger
  , SomeTypeIn DefaultUniUnit
  , SomeTypeIn DefaultUniBool ]
builtinTys _ = []

-- | Generate "small" types at a given kind such as builtins, bound variables, bound datatypes,
-- and abstractions /\ t0 ... tn. T
genAtomicType :: Kind () -> GenTm (Type TyName DefaultUni ())
genAtomicType k = do
  tys <- asks geTypes
  dts <- asks geDatas
  let atoms = [ TyVar () x | (x, k') <- Map.toList tys, k == k' ] ++
              [ TyVar () x | (x, Datatype _ (TyVarDecl _ _ k') _ _ _) <- Map.toList dts, k == k' ]
      builtins = map (TyBuiltin ()) $ builtinTys k
      lam k1 k2 = do
        x <- genMaybeFreshTyName "a"
        TyLam () x k1 <$> bindTyName x k1 (genAtomicType k2)
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

-- | Generate a well-kinded term in a given context
genTypeWithCtx :: Map TyName (Kind ()) -> Kind () -> Gen (Type TyName DefaultUni ())
genTypeWithCtx ctx k = runGenTm $ local (\ e -> e { geTypes = ctx }) (genType k)

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

-- CODE REVIEW: does this exist anywhere?
builtinKind :: SomeTypeIn DefaultUni -> Kind ()
builtinKind (SomeTypeIn t) = case t of
  DefaultUniProtoList -> Star :-> Star
  DefaultUniProtoPair -> Star :-> Star :-> Star
  DefaultUniApply f _ -> let _ :-> k = builtinKind (SomeTypeIn f) in k
  _                   -> Star

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
  | inferKind_ ctx ty == k = ty
  | not $ k `leKind` inferKind_ ctx ty =
      error "fixKind not smaller"
  | otherwise = case ty of
    -- Switch a variable out for a different variable of the right kind
    TyVar _ _ | y : _ <- [ y | (y, k') <- Map.toList ctx
                             , k == k' ] -> TyVar () y
              | otherwise -> minimalType k
    -- Try to fix application by fixing the function
    TyApp _ a b       -> TyApp () (fixKind ctx a $ KindArrow () (inferKind_ ctx b) k) b
    TyLam _ x kx b    ->
      case k of
        -- Fix lambdas to * by getting substituting a minimal type for the argument
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
              kb'  = inferKind_ ctx' b'
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
                         [(k, b)                     | TyLam _ x _ b <- [f], not $ Set.member x (fvType b)] ++
                         [(k, substClosedType x a b) | TyLam _ x _ b <- [f], null (fvType a)] ++
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
      where ka = inferKind_ ctx a
    -- type lambdas shrink by either shrinking the kind of the argument or shrinking the body
    TyLam _ x ka b    -> [ (KindArrow () ka' kb, TyLam () x ka' $ substClosedType x (minimalType ka) b)
                         | ka' <- shrink ka] ++
                         [ (KindArrow () ka kb', TyLam () x ka b)
                         | (kb', b) <- shrinkKindAndType (Map.insert x ka ctx) (kb, b)]
      where KindArrow _ _ kb = k
    TyForall _ x ka b -> [ (k, b) | not $ Set.member x (fvType b) ] ++
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

-- CODE REVIEW: does this exist anywhere?
inferKind :: Map TyName (Kind ()) -> Type TyName DefaultUni () -> Maybe (Kind ())
inferKind ctx ty = case ty of
  TyVar _ x        -> Map.lookup x ctx
  TyFun _ _ _      -> pure $ Star
  TyApp _ a _      -> do KindArrow _ _ k <- inferKind ctx a; pure k
  TyLam _ x k b    -> KindArrow () k <$> inferKind (Map.insert x k ctx) b
  TyForall _ _ _ _ -> pure $ Star
  TyBuiltin _ b    -> pure $ builtinKind b
  TyIFix{}         -> error "inferKind: TyIFix"

-- | Partial inferKind_, useful for context where invariants are set up to guarantee
-- that types are well-kinded.
inferKind_ :: HasCallStack => Map TyName (Kind ()) -> Type TyName DefaultUni () -> Kind ()
inferKind_ ctx ty =
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

data Polarity = Pos
              | Neg
              deriving stock (Ord, Eq, Show)

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
    fvs = Set.unions $ Map.keysSet sub : map fvType (Map.elems sub)

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
        where x' = freshenTyName (fvs <> fvType b) x
      TyForall _ x k b
        | Set.member x fvs -> TyForall () x' k $ go (Set.insert x' fvs) seen sub (renameType x x' b)
        | otherwise        -> TyForall () x  k $ go (Set.insert x fvs) (Set.delete x seen) sub b
        where x' = freshenTyName (fvs <> fvType b) x
      TyBuiltin{}      -> ty
      TyIFix{}         -> error "substType: TyIFix"

-- CODE REVIEW: does this exist anywhere?
renameType :: TyName -> TyName -> Type TyName DefaultUni () -> Type TyName DefaultUni ()
renameType x y | x == y    = id
               | otherwise = substType (Map.singleton x (TyVar () y))

-- CODE REVIEW: this function is a bit strange and I don't like it. Ideas welcome for how to
-- do this better. It basically deals with the fact that we want to be careful when substituting
-- the datatypes that escape from a term into the type. It's yucky but it works.
--
-- This might not be a welcome opinion, but working with this stuff exposes some of
-- the shortcomings of the current PIR design. It would be cleaner if a PIR program was a list
-- of declarations and datatype declarations weren't in terms.
substEscape :: Polarity
            -> Set TyName
            -> Map TyName (Type TyName DefaultUni ())
            -> Type TyName DefaultUni ()
            -> Type TyName DefaultUni ()
substEscape pol fv sub ty = case ty of
  TyVar _ x      -> maybe ty (substEscape pol fv sub) (Map.lookup x sub)
  TyFun _ a b    -> TyFun () (substEscape pol fv sub a) (substEscape pol fv sub b)  -- TODO: pol was Neg
  TyApp _ a b    -> TyApp () (substEscape pol fv sub a) (substEscape pol fv sub b)
  TyLam _ x k b
    | Pos <- pol -> TyLam () x k $ substEscape pol (Set.insert x fv) sub b
    | otherwise  -> TyLam () x' k $ substEscape pol (Set.insert x' fv) sub (renameType x x' b)
    where x' = freshenTyName fv x
  TyForall _ x k b
    | Pos <- pol -> TyForall () x k $ substEscape pol (Set.insert x fv) sub b
    | otherwise  -> TyForall () x' k $ substEscape pol (Set.insert x' fv) sub (renameType x x' b)
    where x' = freshenTyName fv x
  TyBuiltin{}    -> ty
  TyIFix{}       -> ty

-- | Check well-kindedness of a type in a context
checkKind :: Map TyName (Kind ()) -> Type TyName DefaultUni () -> Kind () -> Bool
checkKind ctx ty k = case ty of
  TyVar _ x        -> Just k == Map.lookup x ctx
  TyFun _ a b      -> k == Star && checkKind ctx a k && checkKind ctx b k
  TyApp _ a b | Just kb <- inferKind ctx b -> checkKind ctx a (KindArrow () kb k) && checkKind ctx b kb
              | otherwise                  -> False
  TyLam _ x kx b
    | KindArrow _ ka kb <- k -> kx == ka && checkKind (Map.insert x kx ctx) b kb
    | otherwise              -> False
  TyForall _ x kx b -> k == Star && checkKind (Map.insert x kx ctx) b k
  TyBuiltin _ b    -> k == builtinKind b
  TyIFix{}         -> error "checkKind: TyIFix"

addTmBind :: Binding TyName Name DefaultUni DefaultFun ()
          -> Map Name (Type TyName DefaultUni ())
          -> Map Name (Type TyName DefaultUni ())
addTmBind (TermBind _ _ (VarDecl _ x a) _) = Map.insert x a
addTmBind (DatatypeBind _ dat)             = (Map.fromList (matchType dat : constrTypes dat) <>)
addTmBind _                                = id

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

-- CODE REVIEW: this probably exists somewhere?
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
          -> Maybe (Map TyName (Type TyName DefaultUni ()))
          -- ^ maybe a substitution with domain `flex` that unifies `t1` and `t2`
unifyType ctx flex sub a b = go sub Set.empty (normalizeTy a) (normalizeTy b)
  where
    go sub locals a b =
      case (a, b) of
        (TyVar _ (flip Map.lookup sub -> Just a'), _ ) -> go sub locals a' b
        (_, TyVar _ (flip Map.lookup sub -> Just b') ) -> go sub locals a b'
        (TyVar _ x, TyVar _ y) | x == y                -> pure sub
        (TyVar _ x, b) | validSolve x b                -> pure $ Map.insert x b sub
        (a, TyVar _ y) | validSolve y a                -> pure $ Map.insert y a sub
        (TyFun _ a1 a2, TyFun _ b1 b2 )                -> unifies sub locals [a1, a2] [b1, b2]
        (TyApp _ a1 a2, TyApp _ b1 b2 )                -> unifies sub locals [a1, a2] [b1, b2]
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
        _                                              -> mzero
      where
        validSolve z c = and [Set.member z flex,
                              not $ Set.member z locals,
                              not $ Set.member z fvs,
                              checkKind ctx c (ctx Map.! z),
                              null $ Set.intersection fvs locals
                             ]
          where
            fvs = fvTypeR sub c

    unifies sub _ [] [] = pure sub
    unifies sub locals (a : as) (b : bs) = do
      sub1 <- go sub locals a b
      unifies sub1 locals as bs
    unifies _ _ _ _ = mzero

    fvTypeR sub a = Set.unions $ ns : map (fvTypeR sub . (Map.!) sub) (Set.toList ss)
      where
          fvs = fvType a
          ss  = Set.intersection (Map.keysSet sub) fvs
          ns  = Set.difference fvs ss

-- | Parallel substitution
parSubstType :: Map TyName (Type TyName DefaultUni ())
             -> Type TyName DefaultUni ()
             -> Type TyName DefaultUni ()
parSubstType = substType' False

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
      where Just k = Map.lookup x ctx
    pruneCtx ctx ty = Map.filterWithKey (\ x _ -> Set.member x fvs) ctx
      where fvs = fvType ty

-- | This type keeps track of what kind of argument, term argument (`InstArg`) or
-- type argument (`InstArg`) is required for a function. This type is used primarily
-- with `typeInstTerm` below.when we
-- do unification to figure out if we can get a variable
data TyInst = InstApp (Type TyName DefaultUni ()) | InstArg (Type TyName DefaultUni ())
  deriving stock Show

instance PrettyBy config (Type TyName DefaultUni ()) => PrettyBy config TyInst where
  prettyBy ctx (InstApp ty) = prettyBy ctx ty
  prettyBy ctx (InstArg ty) = brackets (prettyBy ctx ty)

-- | If successful `typeInstTerm n target ty` for an `x :: ty` gives a sequence of `TyInst`s containing `n`
--   `InstArg`s such that `x` instantiated (type application for `InstApp` and applied to a term of
--   the given type for `InstArg`) at the `TyInsts`s has type `target`
typeInstTerm :: HasCallStack
             => Map TyName (Kind ())
             -> Int
             -> Type TyName DefaultUni ()
             -> Type TyName DefaultUni ()
             -> Maybe [TyInst]
typeInstTerm ctx n target ty = do
  sub <- unifyType (ctx <> ctx') flex Map.empty target b
      -- We map any unsolved flexible variables to ∀ a. a
  let defaultSub = minimalType <$> ctx'
      doSub :: HasCallStack => _
      doSub      = substType defaultSub . substType sub
      doSubI (InstApp t) = InstApp (doSub t)
      doSubI (InstArg t) = InstArg (doSub t)
  pure $ map doSubI insts
  where
    fvs = fvType target <> fvType ty <> Map.keysSet ctx
    (ctx', flex, insts, b) = view Map.empty Set.empty [] n fvs ty

    view ctx' flex insts n fvs (TyForall _ x k b) = view (Map.insert x' k ctx') (Set.insert x' flex)
                                                         (InstApp (TyVar () x') : insts) n
                                                         (Set.insert x' fvs) b'
      where (x', b') | Set.member x fvs = let x' = freshenTyName fvs x in (x', renameType x x' b)
                     | otherwise        = (x, b)
    view ctx' flex insts n fvs (TyFun _ a b) | n > 0 = view ctx' flex (InstArg a : insts) (n - 1) fvs b
    view ctx' flex insts _ _ a = (ctx', flex, reverse insts, a)

-- CODE REVIEW: does this exist already?
ceDoc :: Testable t => Doc ann -> t -> Property
ceDoc d = counterexample (show d)

-- CODE REVIEW: does this exist already?
letCE :: (PrettyPir a, Testable p) => String -> a -> (a -> p) -> Property
letCE name x k = ceDoc (fromString name <+> "=" <+> prettyPirReadable x) (k x)

-- CODE REVIEW: does this exist already?
forAllDoc :: (PrettyPir a, Testable p) => String -> Gen a -> (a -> [a]) -> (a -> p) -> Property
forAllDoc name g shr k =
  forAllShrinkBlind g shr $ \ x -> ceDoc (fromString name <+> "=" <+> prettyPirReadable x) (k x)

-- | Check that a list of potential counterexamples is empty and display the
-- list as a QuickCheck counterexample if its not.
checkNoCounterexamples :: PrettyPir [a] => [a] -> Property
checkNoCounterexamples []  = property True
checkNoCounterexamples bad = ceDoc (prettyPirReadable bad) False

genConstant :: SomeTypeIn DefaultUni -> GenTm (Term TyName Name DefaultUni DefaultFun ())
genConstant b = case b of
  SomeTypeIn DefaultUniBool    -> Const DefaultUniBool <$> liftGen arbitrary
  SomeTypeIn DefaultUniInteger -> Const DefaultUniInteger <$> liftGen arbitrary
  SomeTypeIn DefaultUniUnit    -> pure $ Const DefaultUniUnit ()
  SomeTypeIn DefaultUniString  -> Const DefaultUniString . fromString . getPrintableString <$> liftGen arbitrary
  _                            -> error "genConstant"

-- | Try to inhabit a given type in as simple a way as possible,
-- prefers to not default to `error`
inhabitType :: Type TyName DefaultUni () -> GenTm (Term TyName Name DefaultUni DefaultFun ())
inhabitType ty = local (\ e -> e { geTerms = mempty }) $ do
  fromJust <$> runMaybeT (findTm ty <|> pure (Error () ty))
  where
    -- Do the obvious thing as long as target type is not type var
    -- When type var: magic (if higher-kinded type var: black magic)
    -- Ex: get `a` from D ts ==> get `a` from which ts, get which params from D
    -- This function does not fail to error.
    --
    -- NOTE: because we make recursive calls to findTm in this function instead of
    -- inhabitType we don't risk generating terms that are "mostly ok but something is error",
    -- this function will avoid error if possible.
    findTm :: Type TyName DefaultUni () -> MaybeT GenTm (Term TyName Name DefaultUni DefaultFun ())
    findTm (normalizeTy -> ty) = case ty of
      TyFun _ a b -> do
        x <- lift $ genFreshName "x"
        LamAbs () x a <$> mapMaybeT (bindTmName x a) (findTm b)
      TyForall _ x k b -> do
        TyAbs () x k <$> mapMaybeT (bindTyName x k) (findTm b)
      TyBuiltin _ b -> lift $ genConstant b
      -- If we have a type-function application
      (viewApp [] -> (f, _)) ->
        case f of
          TyVar () x  -> do
            _ <- asks geDatas
            asks (Map.lookup x . geDatas) >>= \ case
              -- If the head is a datatype try to inhabit one of its constructors
              Just dat -> foldr mplus mzero $ map (tryCon x ty) (constrTypes dat)
              -- If its not a datatype we try to use whatever bound variables
              -- we have to inhabit the type
              Nothing  -> do
                vars <- asks geTerms
                ctx  <- asks geTypes
                let cands = Map.toList vars
                    -- If we are instantiating something simply instantiate every
                    -- type application with type required by typeInstTerm
                    doInst _ tm (InstApp instTy) = pure $ TyInst () tm instTy
                    -- If we instantiate an application, only succeed if we find
                    -- a non-error argument.
                    doInst _ tm (InstArg argTy)  = Apply () tm <$> findTm argTy
                -- Go over every type and try to inhabit the type at the arguments
                case [ local (\e -> e { geTerms = Map.delete x' (geTerms e) })
                       $ foldM (doInst n) (Var () x') insts
                     | (x', a)    <- cands,
                       n          <- [0..typeArity a],
                       Just insts <- [typeInstTerm ctx n ty a],
                       x `Set.notMember` fvArgs a
                     ] of
                  [] -> mzero
                  gs -> head gs
          _ -> mzero

    -- Try to inhabit a constructor `con` of type `conTy` in datatype `d` at type `ty`
    tryCon d ty (con, conTy)
      | Set.member d (fvArgs conTy) = mzero   -- <- This is ok, since no mutual recursion
      | otherwise = do
          tyctx <- lift $ asks geTypes
          insts <- maybe mzero pure $ typeInstTerm tyctx (typeArity conTy) ty conTy
          let go tm [] = return tm
              go tm (InstApp ty : insts) = go (TyInst () tm ty) insts
              go tm (InstArg ty : insts) = do
                arg <- findTm ty
                go (Apply () tm arg) insts
          go (Var () con) insts

    -- CODE REVIEW: wouldn't it be neat if this existed somewhere?
    viewApp args (TyApp _ f x) = viewApp (x : args) f
    viewApp args ty            = (ty, args)

    -- Get the free variables that appear in arguments of a mixed arrow-forall type
    fvArgs (TyForall _ x _ b) = Set.delete x (fvArgs b)
    fvArgs (TyFun _ a b)      = fvType a <> fvArgs b
    fvArgs _                  = mempty

-- CODE REVIEW: does this exist anywhere?
typeArity :: Num a => Type tyname uni ann -> a
typeArity (TyForall _ _ _ a) = typeArity a
typeArity (TyFun _ _ b)      = 1 + typeArity b
typeArity _                  = 0

-- | Generate as small a term as possible to match a given type.
genAtomicTerm :: Type TyName DefaultUni () -> GenTm (Term TyName Name DefaultUni DefaultFun ())
genAtomicTerm ty = do
  ctx  <- asks geTypes
  vars <- asks geTerms
  -- First try cheap unification
  let unifyVar (x, xty) = typeInstTerm ctx 0 ty xty
                       <&> \ tys -> foldl (TyInst ()) (Var () x) [t | InstApp t <- tys]
  case catMaybes $ map unifyVar $ Map.toList vars of
    -- If unification didn't work try the heavy-handed `inhabitType`.
    -- NOTE: We could probably just replace this whole function with
    -- `inhabitType` and the generators would run fine, but this method
    -- is probably faster a lot of the time and doesn't rely on the
    -- order that thins are chosen `inhabitType`. It is also going to generate
    -- a more even distribution than `inhabitType` (which for performance reasons
    -- always returns the first thing it finds).
    [] -> inhabitType ty
    gs -> liftGen $ elements gs

-- | Generate a term of a given type
genTermOfType :: Type TyName DefaultUni ()
              -> GenTm (Term TyName Name DefaultUni DefaultFun ())
genTermOfType ty = snd <$> genTerm (Just ty)

-- | Generate a term, if the first argument is Nothing then we get something of any type
-- and if the first argument is `Just ty` we get something of type `ty`.
genTerm :: Maybe (Type TyName DefaultUni ())
        -> GenTm (Type TyName DefaultUni (), Term TyName Name DefaultUni DefaultFun ())
genTerm mty = do
  customF <- asks geCustomFreq
  customG <- asks geCustomGen
  vars <- asks geTerms
  esc <- asks geEscaping
  -- Prefer to generate things that bind variables until we have "enough" (20...)
  let (letF, lamF, varAppF) = if Map.size vars < 20
                              then (30, 50, 10)
                              else (10, 30, 40)
      atomic | Just ty <- mty = (ty,) <$> genAtomicTerm ty
             | otherwise      = do ty <- genType Star; (ty,) <$> genAtomicTerm ty
  ifSizeZero atomic $
    frequencyTm $ [ (10, atomic) ]                                             ++
                  [ (letF, genLet mty) ]                                       ++
                  [ (30, genForall x k a) | Just (TyForall _ x k a) <- [mty] ] ++
                  [ (lamF, genLam a b)    | Just (a, b) <- [funTypeView mty] ] ++
                  [ (varAppF, genVarApp mty) ]                                 ++
                  [ (10, genApp mty) ]                                         ++
                  [ (1, genError mty) ]                                        ++
                  [ (10, genConst mty)    | canConst mty ]                     ++
                  [ (10, genDatLet mty)   | YesEscape <- [esc] ]               ++
                  [ (10, genIfTrace)      | isNothing mty ]                    ++
                  [ (customF, customG mty) ]
  where
    funTypeView Nothing                             = Just (Nothing, Nothing)
    funTypeView (Just (normalizeTy -> TyFun _ a b)) = Just (Just a, Just b)
    funTypeView _                                   = Nothing

    -- Generate builtin ifthenelse and trace calls
    genIfTrace = do
      a <- genFreshTyName "a"
      let a' = TyVar () a
      liftGen $ elements [(TyForall () a Star $ TyBuiltin () (SomeTypeIn DefaultUniBool)
                                                  ->> a' ->> a' ->> a'
                          , BIF_If)
                         ,(TyForall () a Star $ TyBuiltin () (SomeTypeIn DefaultUniString)
                                                  ->> a' ->> a'
                          , BIF_Trace)]

    genError Nothing = do
      ty <- genType Star
      return (ty, Error () ty)
    genError (Just ty) = return (ty, Error () ty)

    canConst Nothing            = True
    canConst (Just TyBuiltin{}) = True
    canConst (Just _)           = False

    genConst Nothing = do
      b <- liftGen $ elements $ builtinTys Star
      (TyBuiltin () b,) <$> genConstant b
    genConst (Just ty@(TyBuiltin _ b)) = (ty,) <$> genConstant b
    genConst _ = error "genConst: impossible"

    genDatLet mty = do
      rec <- lift arbitrary
      genDatatypeLet rec $ \ dat -> do
        (ty, tm) <- genTerm mty
        return $ (ty, Let () (if rec then Rec else NonRec) (DatatypeBind () dat :| []) tm)

    genLet mty = do
      -- How many terms to bind
      n   <- liftGen $ choose (1, 3)
      -- Names of the bound terms
      xs  <- genFreshNames $ replicate n "f"
      -- Types of the bound terms
      -- TODO: generate something that matches the target type
      as  <- onSize (`div` 8) $ vecTm n $ genType Star
      -- Strictness
      ss  <- vecTm n $ liftGen $ elements [Strict, NonStrict]
      -- Recursive?
      r   <- liftGen $ frequency [(5, pure True), (30, pure False)]
      -- Generate the binding
      -- TODO: maybe also generate mutually recursive bindings?
      let genBin (x, a) | r         = noEscape . bindTmName x a . genTermOfType $ a
                        | otherwise = noEscape . genTermOfType $ a
      -- Generate both bound terms and body with a size split of 1:7 (note, we are generating up to three bound
      -- terms, so the size split is really something like n:7).
      sizeSplit_ 1 7 (mapM genBin (zip xs as)) (bindTmNames (zip xs as) $ genTerm mty) $ \ tms (ty, body) ->
        let mkBind (x, a, s) tm = TermBind () s
                                    (VarDecl () x a) tm
            b : bs = zipWith mkBind (zip3 xs as ss) tms
        in (ty, Let () (if r then Rec else NonRec) (b :| bs) body)

    genForall x k a = do
      -- TODO: this freshenTyName here might be a bit paranoid
      y <- freshenTyName (fvType a) <$> genFreshTyName "a"
      let ty = TyForall () y k $ renameType x y a
      (ty,) . TyAbs () y k <$> (noEscape . bindTyName y k . genTermOfType $ renameType x y a)

    genLam ma mb = do
      x <- genFreshName "x"
      sizeSplit 1 7 (maybe (genType Star) return ma)
                    (\ a -> bindTmName x a . noEscape $ genTerm mb) $ \ a (b, body) ->
                      (TyFun () a b, LamAbs () x a body)

    genApp mty = noEscape $ sizeSplit 1 4 (genTerm Nothing) (\ (argTy, _) -> genFun argTy mty) $
                  \ (_, arg) (TyFun _ _ resTy, fun) -> (resTy, Apply () fun arg)
      where
        genFun argTy mty = genTerm . Just . TyFun () argTy =<< maybe (genType Star) pure mty

    genVarApp :: HasCallStack => _
    genVarApp Nothing = noEscape $ do
      -- CODE REVIEW: this function exists somewhere maybe? (Maybe even in this module...)
      let arity (TyForall _ _ _ b) = 1 + arity b
          arity (TyFun _ _ b)      = 1 + arity b
          arity _                  = 0

          appl :: HasCallStack => Int -> Term TyName Name DefaultUni DefaultFun () -> _
          appl 0 tm b = return (b, tm)
          appl n tm (TyForall _ x k b) = do
            ty <- genType k
            x' <- genFreshTyName "x"
            appl (n - 1) (TyInst () tm ty) (substType (Map.singleton x' ty) $ renameType x x' b)
          appl n tm (TyFun _ a b) = do
            (_, arg) <- genTerm (Just a)
            appl (n - 1) (Apply () tm arg) b
          appl _ _ _ = error "appl"

          genV (x, ty0) = do
            let ty = normalizeTy ty0
            n <- liftGen $ choose (0, arity ty)
            onSize (`div` n) $ appl n (Var () x) ty
      asks (Map.toList . geTerms) >>= \ case
        []   -> do
          ty <- genType Star
          (ty,) <$> inhabitType ty
        vars -> oneofTm $ map genV vars

    genVarApp (Just ty) = do
      vars <- asks geTerms
      ctx  <- asks geTypes
      let cands = Map.toList vars
          doInst _ tm (InstApp instTy) = pure $ TyInst () tm instTy
          doInst n tm (InstArg argTy)  = onSize ((`div` n) . subtract 1)
                                       . noEscape
                                       $ Apply () tm <$> genTermOfType argTy
      case [ foldM (doInst n) (Var () x) insts
           | (x, a)     <- cands,
             n          <- [0..typeArity a],
             Just insts <- [typeInstTerm ctx n ty a]
           ] of
        [] -> (ty,) <$> inhabitType ty
        gs -> (ty,) <$> oneofTm gs

genDatatypeLet :: Bool -> (Datatype TyName Name DefaultUni DefaultFun () -> GenTm a) -> GenTm a
genDatatypeLet rec cont = do
    k <- liftGen arbitrary
    let kindArgs (k :-> k') = k : kindArgs k'
        kindArgs Star       = []
        ks = kindArgs k
    n <- liftGen $ choose (1, 3)
    ~(d : xs) <- genFreshTyNames $ "d" : replicate (length ks) "a"
    ~(m : cs) <- genFreshNames   $ "m" : replicate n "c"
    let dTy = foldl (TyApp ()) (TyVar () d) [TyVar () x | x <- xs]
        bty d = if rec
                then bindTyName d k
                else registerTyName d
    conArgss <- bty d $ bindTyNames (zip xs ks) $ onSize (`div` n) $ replicateM n $ listTm (genType Star)
    let dat = Datatype () (TyVarDecl () d k) [TyVarDecl () x k | (x, k) <- zip xs ks] m
                       [ VarDecl () c (foldr (->>) dTy conArgs)
                       | (c, _conArgs) <- zip cs conArgss
                       , let conArgs = filter (Set.notMember d . negativeVars) _conArgs]
    bindDat dat $ cont dat

-- | Generate up to 5 datatypes and bind them in a generator.
-- NOTE: despite its name this function does in fact not generate the `Let` binding
-- for the datatypes.
genDatatypeLets :: ([Datatype TyName Name DefaultUni DefaultFun ()] -> GenTm a) -> GenTm a
genDatatypeLets cont = do
  n <- liftGen $ choose (1, 5 :: Int)
  let go 0 k = k []
      go n k = genDatatypeLet False $ \ dat -> go (n - 1) (k . (dat :))
  go n cont

shrinkClosedTypedTerm :: (Type TyName DefaultUni (), Term TyName Name DefaultUni DefaultFun ())
                      -> [(Type TyName DefaultUni (), Term TyName Name DefaultUni DefaultFun ())]
shrinkClosedTypedTerm = shrinkTypedTerm mempty mempty

scopeCheckTyVars :: Map TyName (Kind ())
                 -> (Type TyName DefaultUni (), Term TyName Name DefaultUni DefaultFun ())
                 -> Bool
scopeCheckTyVars tyctx (ty, tm) = all (`Set.member` inscope) (fvType ty)
  where
    inscope = Map.keysSet tyctx <> Set.fromList (map fst $ datatypes tm)

mkHelp :: Map Name (Type TyName DefaultUni ())
       -> Type TyName DefaultUni ()
       -> Term TyName Name DefaultUni DefaultFun ()
mkHelp _ (TyBuiltin _ b)          = minimalBuiltin b
mkHelp (findHelp -> Just help) ty = TyInst () (Var () help) ty
mkHelp _ ty                       = Error () ty

-- | Shrink a typed term in a type and term context.
-- NOTE: if you want to understand what's going on in this function it's a good
-- idea to look at how we do this for types above (it's a lot simpler).
shrinkTypedTerm :: HasCallStack
                => Map TyName (Kind ())
                -> Map Name (Type TyName DefaultUni ())
                -> (Type TyName DefaultUni (), Term TyName Name DefaultUni DefaultFun ())
                -> [(Type TyName DefaultUni (), Term TyName Name DefaultUni DefaultFun ())]
shrinkTypedTerm tyctx ctx (ty, tm) = go tyctx ctx (ty, tm)
  where
    isHelp (Const _ _)            = True
    isHelp (TyInst _ (Var _ x) _) = Just x == findHelp ctx
    isHelp (Error _ _)            = True
    isHelp _                      = False

    addTyBind (TypeBind _ (TyVarDecl _ a k) _)                      = Map.insert a k
    addTyBind (DatatypeBind _ (Datatype _ (TyVarDecl _ a k) _ _ _)) = Map.insert a k
    addTyBind _                                                     = id

    addTyBindSubst (TypeBind _ (TyVarDecl _ a _) ty) = Map.insert a ty
    addTyBindSubst _                                 = id

    go :: HasCallStack => _
    go tyctx ctx (ty, tm) =
      filter (\ (ty, tm) -> scopeCheckTyVars tyctx (ty, tm)) $
      nonstructural tyctx ctx (ty, tm) ++
      structural    tyctx ctx (ty, tm)

    -- These are the special cases and "tricks" for shrinking
    nonstructural :: HasCallStack => _
    nonstructural tyctx ctx (ty, tm) =
      [ (ty', tm') | not $ isHelp tm
                   , ty' <- ty : shrinkType (tyctx <> Map.fromList (datatypes tm)) ty
                   , let tm' = mkHelp ctx ty' ] ++
      case tm of

        -- TODO: shrink Rec to NonRec
        Let _ rec binds body ->
          [ (letTy, letTm)
          | (_, TermBind _ _ (VarDecl _ _ letTy) letTm) <- oneHoleContexts binds
          , rec == NonRec
          ] ++
          [ case binds0 ++ binds1 of
              []         -> fixupTerm_ tyctxInner ctxInner tyctxInner' ctxInner' ty body
              b : binds' -> second (Let () rec (b :| binds'))
                          $ fixupTerm_ tyctxInner ctxInner tyctxInner' ctxInner' ty body
          | (NonEmptyContext binds0 binds1, _) <- oneHoleContexts binds,
            let tyctxInner  = foldr addTyBind tyctx binds
                ctxInner    = foldr addTmBind ctx   binds
                tyctxInner' = foldr addTyBind tyctx (binds0 ++ binds1)
                ctxInner'   = foldr addTmBind ctx   (binds0 ++ binds1)
          ] ++
          [ fixupTerm_ tyctxInner ctxInner tyctx ctx ty body
          | let tyctxInner  = foldr addTyBind tyctx binds
                ctxInner    = foldr addTmBind ctx   binds ]

        LamAbs _ x a body ->
          [ fixupTerm_ tyctx (Map.insert x a ctx) tyctx ctx b body
          | TyFun _ _ b <- [ty] ] ++
          [ (b, body)
          | TyFun _ _ b <- [ty]
          , x `Set.notMember` fvTerm body ]

        Apply _ fun arg | Just argTy <- inferTypeInContext tyctx ctx arg ->
          -- Drop substerms
          [(argTy, arg), (TyFun () argTy ty, fun)] ++
          -- Shrink subterms (TODO: this is really two-step shrinking and might not be necessary)
          go tyctx ctx (TyFun () argTy ty, fun) ++
          go tyctx ctx (argTy, arg)

        TyAbs _ x _ body ->
          [ fixupTerm_ (Map.insert x k tyctx) ctx tyctx ctx tyInner' body
          | TyForall _ y k tyInner <- [ty]
          , let tyInner' = substClosedType y (minimalType k) tyInner
          ]

        -- Builtins can shrink to unit. More fine-grained shrinking is in `structural` below.
        Const DefaultUniBool _ ->
          [ (TyBuiltin () (SomeTypeIn DefaultUniUnit), Const DefaultUniUnit ()) ]
        Const DefaultUniInteger _ ->
          [ (TyBuiltin () (SomeTypeIn DefaultUniUnit), Const DefaultUniUnit ()) ]
        Const DefaultUniString _ ->
          [ (TyBuiltin () (SomeTypeIn DefaultUniUnit), Const DefaultUniUnit ()) ]
        Const b _ -> [ (TyBuiltin () (SomeTypeIn b), bin) | bin <- [ minimalBuiltin (SomeTypeIn b) ]
                                                          , bin /= tm ]

        _ -> []

    -- These are the structural (basically homomorphic) cases in shrinking.
    -- They all just try to shrink a single subterm at a time. We also
    -- use fixupTerm to adjust types here in a trick similar to how we shrunk
    -- types above.
    structural :: HasCallStack => _
    structural tyctx ctx (ty, tm) =
      case tm of

        Let _ rec binds body ->
          [ (parSubstType subst ty', Let () rec binds body')
          | (ty', body') <- go tyctxInner ctxInner (ty, body) ] ++
          [ fix $ second (Let () rec binds') $ fixupTerm_ tyctxInner ctxInner tyctxInner' ctxInner' ty body
            | (context@(NonEmptyContext before _), bind) <- oneHoleContexts binds,
              let ctxBind | Rec <- rec = ctxInner
                          | otherwise  = foldr addTmBind ctx before
                  tyctxBind | Rec <- rec = tyctxInner
                            | otherwise  = foldr addTyBind tyctx before,
              bind' <- shrinkBind rec tyctxBind ctxBind bind,
              let binds'      = plugHole context bind'
                  tyctxInner' = foldr addTyBind tyctx binds'
                  ctxInner'   = foldr addTmBind ctx   binds'
                  fix | Rec <- rec = uncurry (fixupTerm_ tyctxInner ctxInner tyctxInner ctxInner)
                      | otherwise  = id
          ] where subst = foldr addTyBindSubst mempty binds
                  tyctxInner = foldr addTyBind tyctx binds
                  ctxInner   = foldr addTmBind ctx binds

        TyInst _ fun argTy ->
          [ (substType (Map.singleton x argTy') tyInner', TyInst () fun' argTy')
          | (k', argTy') <- shrinkKindAndType tyctx (k, argTy)
          , let tyInner' | k == k'   = tyInner
                         -- TODO: use proper fixupType
                         | otherwise = substType (Map.singleton x $ minimalType k) tyInner
                fun' = fixupTerm tyctx ctx tyctx ctx (TyForall () x k' tyInner') fun
          ] where Just (TyForall _ x k tyInner) = inferTypeInContext tyctx ctx fun

        TyAbs _ x _ body | not $ Map.member x tyctx ->
          [ (TyForall () x k tyInner', TyAbs () x k body')
          | TyForall _ y k tyInner <- [ty]
          , (tyInner', body') <- go (Map.insert x k tyctx) ctx (renameType y x tyInner, body)
          ]

        LamAbs _ x a body ->
          [ (TyFun () a b', LamAbs () x a body')
          | TyFun _ _ b <- [ty],
            (b', body') <- go tyctx (Map.insert x a ctx) (b, body)
          ] ++
          [ (TyFun () a' *** LamAbs () x a') $ fixupTerm_ tyctx (Map.insert x a ctx)
                                                          tyctx (Map.insert x a' ctx) b body
          | TyFun _ _ b <- [ty],
            a' <- shrinkType tyctx a
          ]

        Apply _ fun arg ->
          [ (ty', Apply () fun' arg')
          | Just argTy <- [inferTypeInContext tyctx ctx arg]
          , (TyFun _ argTy' ty', fun') <- go tyctx ctx (TyFun () argTy ty, fun)
          , let arg' = fixupTerm tyctx ctx tyctx ctx argTy' arg
          ] ++
          [ (ty,  Apply () fun' arg')
          | Just argTy <- [inferTypeInContext tyctx ctx arg]
          , (argTy', arg') <- go tyctx ctx (argTy, arg)
          , let fun' = fixupTerm tyctx ctx tyctx ctx (TyFun () argTy' ty) fun
          ]

        Const DefaultUniBool b ->
          [ (ty, Const DefaultUniBool b') | b' <- shrink b ]

        Const DefaultUniInteger i ->
          [ (ty, Const DefaultUniInteger i') | i' <- shrink i ]

        _ -> []

-- | Try to infer the type of an expression in a given type and term context.
-- NOTE: one can't just use out-of-the-box type inference here because the
-- `inferType` algorithm happy renames things.
inferTypeInContext :: Map TyName (Kind ())
                   -> Map Name (Type TyName DefaultUni ())
                   -> Term TyName Name DefaultUni DefaultFun ()
                   -> Maybe (Type TyName DefaultUni ())
inferTypeInContext tyctx ctx tm = either (const Nothing) Just
                                $ runQuoteT @(Either (Error DefaultUni DefaultFun ())) $ do
  -- CODE REVIEW: this algorithm is fragile, it relies on knowing that `inferType`
  -- does renaming to compute the `esc` substitution for datatypes. However, there is also
  -- not any other way to do this in a way that makes type inference actually useful - you
  -- want to do type inference in non-top-level contexts. Ideally I think type inference
  -- probably shouldn't do renaming of datatypes... Or alternatively we need to ensure that
  -- the renaming behaviour of type inference is documented and maintained.
  cfg <- getDefTypeCheckConfig ()
  -- Infer the type of `tm` by adding the contexts as (type and term) lambdas
  Normalized _ty' <- runQuoteT $ inferType cfg tm'
  -- Substitute the free variables and escaping datatypes to get back to the un-renamed type.
  let ty' = substEscape Pos (Map.keysSet esc <> foldr (<>) (fvType _ty') (fvType <$> esc)) esc _ty' -- yuck
  -- Get rid of the stuff we had to add for the context.
  return $ stripFuns tms $ stripForalls mempty tys ty'
  where
    tm' = addTyLams tys $ addLams tms tm
    rntm = case runQuoteT $ rename tm' of
      Left _     -> error "impossible"
      Right tm'' -> tm''

    -- Compute the substitution that takes datatypes that escape
    -- the scope in the inferred type (given by computing them from the
    -- renamed term) and turns them into datatypes in the old type.
    esc = Map.fromList (zip dats' $ map (TyVar ()) dats)

    dats' = map fst $ datatypes rntm
    dats = map fst $ datatypes tm'

    tys = Map.toList tyctx
    tms = Map.toList ctx

    addTyLams [] tm            = tm
    addTyLams ((x, k) : xs) tm = TyAbs () x k $ addTyLams xs tm

    addLams [] tm             = tm
    addLams ((x, ty) : xs) tm = LamAbs () x ty $ addLams xs tm

    stripForalls sub [] ty                            = parSubstType sub ty
    stripForalls sub ((x, _) : xs) (TyForall _ y _ b) = stripForalls (Map.insert y (TyVar () x) sub) xs b
    stripForalls _ _ _                                = error "stripForalls"

    stripFuns [] ty                  = ty
    stripFuns (_ : xs) (TyFun _ _ b) = stripFuns xs b
    stripFuns _ _                    = error "stripFuns"

-- | Compute the datatype declarations that escape from a term.
datatypes :: Term TyName Name DefaultUni DefaultFun ()
          -> [(TyName, (Kind ()))]
datatypes tm = case tm of
  Var _ _           -> mempty
  Builtin _ _       -> mempty
  Constant _ _      -> mempty
  Apply _ _ _       -> mempty
  LamAbs _ _ _ tm'  -> datatypes tm'
  TyAbs _ _ _ tm'   -> datatypes tm'
  TyInst _ _ _    -> mempty
  Let _ _ binds tm' -> foldr addDatatype (datatypes tm') binds
    where
      addDatatype (DatatypeBind _ (Datatype _ (TyVarDecl _ a k) _ _ _)) = ((a, k):)
      addDatatype _                                                     = id
  Error _ _ -> mempty
  _ -> error "nope"

findHelp :: Map Name (Type TyName DefaultUni ()) -> Maybe Name
findHelp ctx =
  case Map.toList $ Map.filter isHelpType ctx of
    []         -> Nothing
    (x, _) : _ -> Just x
  where
    isHelpType (TyForall _ x Star (TyVar _ x')) = x == x'
    isHelpType _                                = False

-- | Try to take a term from an old context to a new context and a new type.
-- If we can't do the new type we might return a different type.
fixupTerm_ :: Map TyName (Kind ())
           -> Map Name (Type TyName DefaultUni ())
           -> Map TyName (Kind ())
           -> Map Name (Type TyName DefaultUni ())
           -> Type TyName DefaultUni ()
           -> Term TyName Name DefaultUni DefaultFun ()
           -> (Type TyName DefaultUni (), Term TyName Name DefaultUni DefaultFun ())
fixupTerm_ tyctxOld ctxOld tyctxNew ctxNew tyNew tm =
  case inferTypeInContext tyctxNew ctxNew tm of
    Nothing -> case tm of
      LamAbs _ x a tm | TyFun () _ b <- tyNew -> (a ->>) *** (LamAbs () x a)
                                              $ fixupTerm_ tyctxOld (Map.insert x a ctxOld)
                                                           tyctxNew (Map.insert x a ctxNew) b tm
      Apply _ (Apply _ (TyInst _ BIF_Trace _) s) tm ->
        let (ty', tm') = fixupTerm_ tyctxOld ctxOld tyctxNew ctxNew tyNew tm
        in (ty', Apply () (Apply () (TyInst () BIF_Trace ty') s) tm')
      _ | TyBuiltin _ b <- tyNew -> (tyNew, minimalBuiltin b)
        | otherwise -> (tyNew, mkHelp ctxNew tyNew)
    Just ty -> (ty, tm)

-- | Try to take a term from an old context to a new context and a new type - default to `mkHelp`.
fixupTerm :: Map TyName (Kind ())
          -> Map Name (Type TyName DefaultUni ())
          -> Map TyName (Kind ())
          -> Map Name (Type TyName DefaultUni ())
          -> Type TyName DefaultUni ()
          -> Term TyName Name DefaultUni DefaultFun ()
          -> Term TyName Name DefaultUni DefaultFun ()
fixupTerm _ _ tyctxNew ctxNew tyNew tm
  | typeCheckTermInContext tyctxNew ctxNew tm tyNew = tm
  | otherwise                                       = mkHelp ctxNew tyNew

minimalBuiltin :: SomeTypeIn DefaultUni -> Term TyName Name DefaultUni DefaultFun ()
minimalBuiltin (SomeTypeIn b@DefaultUniUnit)    = Const b ()
minimalBuiltin (SomeTypeIn b@DefaultUniInteger) = Const b 0
minimalBuiltin (SomeTypeIn b@DefaultUniBool)    = Const b False
minimalBuiltin (SomeTypeIn b@DefaultUniString)  = Const b ""
minimalBuiltin b                                = error $ "minimalBuiltin: " ++ show b

shrinkBind :: HasCallStack
           => Recursivity
           -> Map TyName (Kind ())
           -> Map Name (Type TyName DefaultUni ())
           -> Binding TyName Name DefaultUni DefaultFun ()
           -> [Binding TyName Name DefaultUni DefaultFun ()]
shrinkBind _ tyctx ctx bind =
  case bind of
    -- Note: this is a bit tricky for recursive binds, if we change a recursive bind we need to fixup all
    -- the other binds in the block. Currently we do this with a fixupTerm_ in the structural part of shrinking.
    --
    -- In the future this can be made better if we find properties where lets don't shrink well enough to be
    -- understandable.
    TermBind _ s (VarDecl _ x ty) tm -> [ TermBind () s (VarDecl () x ty') tm'
                                        | (ty', tm') <- shrinkTypedTerm tyctx ctx (ty, tm)
                                        ] ++
                                        [ TermBind () Strict (VarDecl () x ty) tm | s == NonStrict ]
    -- These cases are basically just structural
    TypeBind _ (TyVarDecl _ a k) ty  -> [ TypeBind () (TyVarDecl () a k') ty'
                                        | (k', ty') <- shrinkKindAndType tyctx (k, ty) ]
    DatatypeBind _ dat               -> [ DatatypeBind () dat' | dat' <- shrinkDat tyctx dat ]

shrinkDat :: Map TyName (Kind ())
          -> Datatype TyName Name DefaultUni DefaultFun ()
          -> [Datatype TyName Name DefaultUni DefaultFun ()]
shrinkDat ctx (Datatype _ dd@(TyVarDecl _ d _) xs m cs) =
  [ Datatype () dd xs m cs' | cs' <- shrinkList shrinkCon cs ]
  where
    ctx' = ctx <> Map.fromList [ (x, k) | TyVarDecl _ x k <- xs ]
    shrinkCon (VarDecl _ c ty) = [ VarDecl () c ty''
                                 | ty' <- shrinkType ctx' ty
                                 , let ty'' = setTarget (getTarget ty) ty'
                                 , ty'' /= ty
                                 , d `Set.notMember` positiveVars (setTarget unit ty') ]
      where
        getTarget (TyFun _ _ b) = getTarget b
        getTarget b             = b
        setTarget t (TyFun _ a b) = TyFun () a (setTarget t b)
        setTarget t _             = t

genTypeAndTerm_ :: Gen (Type TyName DefaultUni (), Term TyName Name DefaultUni DefaultFun ())
genTypeAndTerm_ = runGenTm $ do
  (ty, body) <- genTerm Nothing
  return (ty, body)

-- | Take a term of a specified type and generate
-- a fully applied term. Useful for generating terms that you want
-- to stick directly in an interpreter. Prefers to generate small arguments.
-- NOTE: The logic of this generating small arguments is that the inner term
-- should already have plenty of complicated arguments to functions to begin
-- with and now we just want to fill out the arguments so that we get
-- something that hopefully evaluates for a non-trivial number of steps.
genFullyApplied :: Type TyName DefaultUni ()
                -> Term TyName Name DefaultUni DefaultFun ()
                -> Gen (Type TyName DefaultUni (), Term TyName Name DefaultUni DefaultFun ())
genFullyApplied typ trm = runGenTm $ go trm
  where
    go trm = case trm of
      Let () rec binds body -> second (Let () rec binds) <$> bindBinds binds (go body)
      _                     -> genArgsApps typ trm
    genArgsApps (TyForall _ x k typ) trm = do
      let ty = minimalType k
      genArgsApps (substClosedType x ty typ) (TyInst () trm ty)
    genArgsApps (TyFun _ a b) trm = do
      (_, arg) <- noEscape $ genTerm (Just a)
      genArgsApps b (Apply () trm arg)
    genArgsApps ty trm = return (ty, trm)

-- | Generate a term of a specific type given a type and term context
genTermInContext_ :: Map TyName (Kind ())
                  -> Map Name (Type TyName DefaultUni ())
                  -> Type TyName DefaultUni ()
                  -> Gen (Term TyName Name DefaultUni DefaultFun ())
genTermInContext_ tyctx ctx ty =
  runGenTm $ local (\ e -> e { geTypes = tyctx, geTerms = ctx, geEscaping = NoEscape }) $
    snd <$> genTerm (Just ty)

typeCheckTerm :: Term TyName Name DefaultUni DefaultFun ()
              -> Type TyName DefaultUni ()
              -> Bool
typeCheckTerm = typeCheckTermInContext Map.empty Map.empty

typeCheckTermInContext :: Map TyName (Kind ())
                       -> Map Name (Type TyName DefaultUni ())
                       -> Term TyName Name DefaultUni DefaultFun ()
                       -> Type TyName DefaultUni ()
                       -> Bool
typeCheckTermInContext tyctx ctx tm ty = isJust $ do
    ty' <- inferTypeInContext tyctx ctx tm
    unifyType tyctx mempty mempty ty' ty

-- CODE REVIEW: Do these functions exist in a convenient package anywhere?
var :: String -> Int -> Name
var s i = Name (fromString s) (toEnum i)

tyvar :: String -> Int -> TyName
tyvar s i = TyName (var s i)

unit :: Type tyname DefaultUni ()
unit = TyBuiltin () (SomeTypeIn DefaultUniUnit)

integer :: Type tyname DefaultUni ()
integer = TyBuiltin () (SomeTypeIn DefaultUniInteger)

bool :: Type tyname DefaultUni ()
bool = TyBuiltin () (SomeTypeIn DefaultUniBool)

-- Containers (zipper-ish, very useful for shrinking.)
-- CODE REVIEW: should these go elsewhere? Do these already exist somewhere?

class Container f where
  data OneHoleContext f :: * -> *
  oneHoleContexts :: f a -> [(OneHoleContext f a, a)]
  plugHole :: OneHoleContext f a -> a -> f a

instance Container [] where
  data OneHoleContext [] a = ListContext [a] [a]
  oneHoleContexts (x : xs) = (ListContext [] xs, x) : [ (ListContext (x : ys) zs, y)
                                                      | (ListContext ys zs, y) <- oneHoleContexts xs ]
  oneHoleContexts []       = []
  plugHole (ListContext xs ys) z = xs ++ [z] ++ ys

instance Container NonEmpty where
  data OneHoleContext NonEmpty a = NonEmptyContext [a] [a]
  oneHoleContexts (x :| xs) = (NonEmptyContext [] xs, x) : [ (NonEmptyContext (x : ys) zs, y)
                                                           | (ListContext ys zs, y) <- oneHoleContexts xs ]
  plugHole (NonEmptyContext []       ys) z = z :| ys
  plugHole (NonEmptyContext (x : xs) ys) z = x :| xs ++ [z] ++ ys

-- CODE REVIEW: where to put the stuff below? Can we refactor to the point where we don't need them?
-- Currently we need these for shrinking, getting rid of them would be nice.
deriving stock instance Eq (Term TyName Name DefaultUni DefaultFun ())
deriving stock instance Eq (Binding TyName Name DefaultUni DefaultFun ())
deriving stock instance Eq (VarDecl TyName Name DefaultUni DefaultFun ())
deriving stock instance Eq (TyVarDecl TyName ())
deriving stock instance Eq (Datatype TyName Name DefaultUni DefaultFun ())

-- Some convenience definitions that make the code slightly more readable.
{-# COMPLETE Star, (:->) #-}
pattern Star :: Kind ()
pattern Star  = Type ()

pattern (:->) :: Kind () -> Kind () -> Kind ()
pattern (:->) a b = KindArrow () a b
infixr 3 :->

pattern BIF_Trace :: Term tyname name uni DefaultFun ()
pattern BIF_Trace = Builtin () Trace

pattern BIF_If :: Term tyname name uni DefaultFun ()
pattern BIF_If = Builtin () IfThenElse

pattern Const :: DefaultUni (Esc a) -> a -> Term tyname name DefaultUni fun ()
pattern Const b a = Constant () (Some (ValueOf b a))

infixr 3 ->>
(->>) :: (Type TyName DefaultUni ()) -> (Type TyName DefaultUni ()) -> (Type TyName DefaultUni ())
(->>) = TyFun ()

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

-- CODE REVIEW: this should probably go elsewhere?
instance PrettyBy config i => PrettyBy config (NonNegative i) where
  prettyBy ctx (NonNegative i) = prettyBy ctx i

-- CODE REVIEW: this should probably go elsewhere?
instance ( HasPrettyDefaults config ~ 'True
         , PrettyBy config k
         , PrettyBy config v) => PrettyBy config (Map k v) where
  prettyBy ctx = prettyBy ctx . Map.toList
