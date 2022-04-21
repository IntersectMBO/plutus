{-# LANGUAGE BangPatterns          #-}
{-# LANGUAGE ConstraintKinds       #-}
{-# LANGUAGE DeriveAnyClass        #-}
{-# LANGUAGE DeriveFunctor         #-}
{-# LANGUAGE DerivingVia           #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE ImportQualifiedPost   #-}
{-# LANGUAGE LambdaCase            #-}
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

module PlutusCore.Generators.PIR where

import Codec.Serialise
import Control.Applicative ((<|>))
import Control.Arrow hiding ((<+>))
import Control.DeepSeq
import Control.Lens (set, (&), (<&>), (^.))
import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.Trans.Maybe
import Data.ByteString.Lazy (toStrict)
import Data.ByteString.Short (toShort)
import Data.Char
import Data.Either
import Data.Foldable
import Data.List hiding (insert)
import Data.List.NonEmpty (NonEmpty (..))
import Data.Map (Map)
import Data.Map qualified as Map
import Data.Maybe
import Data.Ord
import Data.Set (Set)
import Data.Set qualified as Set
import Data.String
import Data.Text qualified as Text
import GHC.Stack
import GHC.Word
import PlutusCore (typeSize)
import PlutusCore.DeBruijn hiding (DeBruijn)
import PlutusCore.Default
import PlutusCore.Name
import PlutusCore.Normalize
import PlutusCore.Quote (runQuoteT)
import PlutusCore.Rename
import PlutusIR
import PlutusIR.Compiler
import PlutusIR.Error
import PlutusIR.TypeCheck
import System.IO.Unsafe
import System.Timeout
import Test.QuickCheck
import Text.Printf
import Text.Read (readMaybe)

import PlutusCore qualified as PLC
import PlutusIR.Compiler qualified as PIR
import UntypedPlutusCore qualified as UPLC

import Test.Tasty (TestTree, testGroup)
import Test.Tasty.QuickCheck hiding (Success)

debug :: Bool
debug = False

data GenEnv = GenEnv
  { geSize               :: Int
  , geHelp               :: Maybe (Term TyName Name DefaultUni DefaultFun ())   -- help : ∀ a. a
  , geDatas              :: Map TyName (Datatype TyName Name DefaultUni DefaultFun ())
  , geTypes              :: Map TyName (Kind ())
  , geTerms              :: Map Name (Type TyName DefaultUni ())
  , geUnboundUsedTyNames :: Set TyName
  , geEscaping           :: AllowEscape
  }

type GenTm = ReaderT GenEnv Gen

liftGen :: Gen a -> GenTm a
liftGen gen = do
  sz <- asks geSize
  lift $ resize sz gen

liftGenF :: Functor f => (f (Gen a) -> Gen a) -> f (GenTm a) -> GenTm a
liftGenF oo gs = ReaderT $ \ env -> oo $ fmap (`runReaderT` env) gs

onSize :: (Int -> Int) -> GenTm a -> GenTm a
onSize f = local $ \ env -> env { geSize = f (geSize env) }

ifSizeZero :: GenTm a -> GenTm a -> GenTm a
ifSizeZero ifZ nonZ = do
  n <- asks geSize
  if n <= 0 then ifZ else nonZ

withSize :: Int -> GenTm a -> GenTm a
withSize = onSize . const

sizeSplit_ :: Int -> Int -> GenTm a -> GenTm b -> (a -> b -> c) -> GenTm c
sizeSplit_ a b ga gb = sizeSplit a b ga (const gb)

sizeSplit :: Int -> Int -> GenTm a -> (a -> GenTm b) -> (a -> b -> c) -> GenTm c
sizeSplit a b ga gb f = do
  n <- asks geSize
  let na = (a * n) `div` (a + b)
      nb = (b * n) `div` (a + b)
  x <- withSize na ga
  f x <$> withSize nb (gb x)

newtype FreqList a = FreqList { unFreqList :: [(Int, a)] }
  deriving Functor

frequencyTm :: [(Int, GenTm a)] -> GenTm a
frequencyTm = liftGenF (frequency . unFreqList) . FreqList

listTm :: GenTm a -> GenTm [a]
listTm g = do
  sz <- asks geSize
  n  <- liftGen $ choose (0, div sz 3)
  onSize (`div` n) $ replicateM n g

runGenTm :: GenTm a -> Gen a
runGenTm g = sized $ \ n ->
  runReaderT g $ GenEnv { geSize               = n
                        , geHelp               = Just $ Var () $ Name "help" (toEnum 0)
                        , geDatas              = Map.empty
                        , geTypes              = Map.empty
                        , geTerms              = Map.empty
                        , geUnboundUsedTyNames = Set.empty
                        , geEscaping           = YesEscape
                        }

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

-- TODO: fix this to allow us to be flexible with locations
pattern LIT_Loc :: String -> Term tyname name DefaultUni fun ()
pattern LIT_Loc l <- Const DefaultUniString (Text.unpack -> l)

infixr 3 ->>
(->>) :: (Type TyName DefaultUni ()) -> (Type TyName DefaultUni ()) -> (Type TyName DefaultUni ())
(->>) = TyFun ()

instance Arbitrary (Kind ()) where
  arbitrary = sized $ arb . (`div` 3)
    where
      arb 0 = pure $ Star
      arb n = frequency [(4, pure $ Star),
                         (1, (:->) <$> arb (div n 6) <*> arb (div (5 * n) 6))]
  shrink Star      = []
  shrink (a :-> b) = [b] ++ [a' :-> b' | (a', b') <- shrink (a, b)]
    -- Note: `a` can have bigger arity than `a -> b` so don't shrink to it!

getUniques :: GenTm (Set Unique)
getUniques = do
  GenEnv{geDatas = dts, geTypes = tys, geTerms = tms, geUnboundUsedTyNames = used} <- ask
  return $ Set.mapMonotonic (nameUnique . unTyName) (Map.keysSet dts <> Map.keysSet tys <> used) <>
           Set.mapMonotonic nameUnique (Map.keysSet tms) <>
           Set.unions [ names d | d <- Map.elems dts ]
  where
    names (Datatype _ _ _ m cs) = Set.fromList $ nameUnique m : [ nameUnique c | VarDecl _ c _ <- cs ]

genFreshName :: String -> GenTm Name
genFreshName s = head <$> genFreshNames [s]

genFreshNames :: [String] -> GenTm [Name]
genFreshNames ss = do
  used <- getUniques
  let i = fromEnum $ Set.findMax $ Set.insert (Unique 0) used
      js = [ j | j <- [1..i], not $ Unique j `Set.member` used ]
      is = js ++ take (length ss + 10) [i+1..]
  is' <- liftGen $ shuffle is
  return [Name (fromString $ s ++ show j) (toEnum j) | (s, j) <- zip ss is']

genFreshTyName :: String -> GenTm TyName
genFreshTyName s = TyName <$> genFreshName s

genFreshTyNames :: [String] -> GenTm [TyName]
genFreshTyNames ss = map TyName <$> genFreshNames ss

genNotFreshName :: String -> GenTm Name
genNotFreshName s = do
  used <- Set.toList <$> getUniques
  case used of
    [] -> genFreshName s
    _  -> liftGen $ elements [ Name (fromString $ s ++ show (unUnique i)) i | i <- used ]

genMaybeFreshName :: String -> GenTm Name
genMaybeFreshName s = frequencyTm [(3, genFreshName s), (1, genNotFreshName s)]

genMaybeFreshTyName :: String -> GenTm TyName
genMaybeFreshTyName s = TyName <$> genMaybeFreshName s

fvTypeBag :: (Type TyName DefaultUni ()) -> Map TyName Int
fvTypeBag ty = case ty of
  TyVar _ x        -> Map.singleton x 1
  TyFun _ a b      -> Map.unionWith (+) (fvTypeBag a) (fvTypeBag b)
  TyApp _ a b      -> Map.unionWith (+) (fvTypeBag a) (fvTypeBag b)
  TyLam _ x _ b    -> Map.delete x (fvTypeBag b)
  TyForall _ x _ b -> Map.delete x (fvTypeBag b)
  TyBuiltin{}      -> Map.empty
  TyIFix{}         -> error "fvTypeBag: TyIFix"

fvType :: (Type TyName DefaultUni ()) -> Set TyName
fvType = Map.keysSet . fvTypeBag

bindTyName :: TyName -> (Kind ()) -> GenTm a -> GenTm a
bindTyName x k = local $ \ e -> e { geTypes = Map.insert x k (geTypes e)
                                  , geTerms = Map.filter (\ty -> not $ x `Set.member` fvType ty) (geTerms e)
                                  , geDatas = Map.delete x (geDatas e)
                                  }

bindTyNames :: [(TyName, (Kind ()))] -> GenTm a -> GenTm a
bindTyNames = flip $ foldr (uncurry bindTyName)

registerTyName :: TyName -> GenTm a -> GenTm a
registerTyName n = local $ \ e -> e { geUnboundUsedTyNames = Set.insert n (geUnboundUsedTyNames e) }

bindTmName :: Name -> (Type TyName DefaultUni ()) -> GenTm a -> GenTm a
bindTmName x ty = local $ \ e -> e { geTerms = Map.insert x ty (geTerms e) }

bindTmNames :: [(Name, (Type TyName DefaultUni ()))] -> GenTm a -> GenTm a
bindTmNames = flip $ foldr (uncurry bindTmName)

bindFreshTmName :: String -> (Type TyName DefaultUni ()) -> (Name -> GenTm a) -> GenTm a
bindFreshTmName name ty k = do
  x <- genFreshName name
  bindTmName x ty (k x)

constrTypes :: (Datatype TyName Name DefaultUni DefaultFun ()) -> [(Name, (Type TyName DefaultUni ()))]
constrTypes (Datatype _ _ xs _ cs) = [ (c, abstr ty) | VarDecl _ c ty <- cs ]
  where
    abstr ty = foldr (\ (TyVarDecl _ x k) -> TyForall () x k) ty xs

freshenTyName :: Set TyName -> TyName -> TyName
freshenTyName fvs (TyName (Name x j)) = TyName (Name x i)
  where i  = succ $ Set.findMax is
        is = Set.insert j $ Set.insert (toEnum 0) $ Set.mapMonotonic (nameUnique . unTyName) fvs

matchType :: (Datatype TyName Name DefaultUni DefaultFun ()) -> (Name, (Type TyName DefaultUni ()))
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

bindDat :: Datatype TyName Name DefaultUni DefaultFun ()
        -> GenTm a
        -> GenTm a
bindDat dat@(Datatype _ (TyVarDecl _ a k) _ _ _) cont =
  bindTyName a k $
  local (\ e -> e { geDatas = Map.insert a dat (geDatas e) }) $
  foldr (uncurry bindTmName) cont (matchType dat : constrTypes dat)

bindBind :: Binding TyName Name DefaultUni DefaultFun ()
         -> GenTm a
         -> GenTm a
bindBind (DatatypeBind _ dat)              = bindDat dat
bindBind (TermBind _ _ (VarDecl _ x ty) _) = bindTmName x ty
bindBind _                                 = error "unreachable"

bindBinds :: Foldable f => f (Binding TyName Name DefaultUni DefaultFun ()) -> GenTm a -> GenTm a
bindBinds = flip (foldr bindBind)

builtinTys :: (Kind ()) -> [SomeTypeIn DefaultUni]
builtinTys Star =
  [ SomeTypeIn DefaultUniInteger
  , SomeTypeIn DefaultUniUnit
  , SomeTypeIn DefaultUniBool ]
builtinTys _ = []

genAtomicType :: (Kind ()) -> GenTm (Type TyName DefaultUni ())
genAtomicType k = do
  tys <- asks geTypes
  dts <- asks geDatas
  let atoms = [ TyVar () x | (x, k') <- Map.toList tys, k == k' ] ++
              [ TyVar () x | (x, Datatype _ (TyVarDecl _ _ k') _ _ _) <- Map.toList dts, k == k' ]
      builtins = map (TyBuiltin ()) $ builtinTys k
      lam k1 k2 = do
        x <- genMaybeFreshTyName "a"
        TyLam () x k1 <$> bindTyName x k1 (genAtomicType k2)
  liftGenF oneof $ map pure (atoms ++ builtins) ++ [lam k1 k2 | KindArrow _ k1 k2 <- [k]]

genType :: (Kind ()) -> GenTm (Type TyName DefaultUni ())
genType k = onSize (min 10) $
  ifSizeZero (genAtomicType k) $
    frequencyTm $ [ (1, genAtomicType k) ] ++
                  [ (2, sizeSplit_ 1 7 (genType k) (genType k) (TyFun ())) | k == Star ] ++
                  [ (1, genForall) | k == Star ] ++
                  [ (1, genLam k1 k2) | KindArrow _ k1 k2 <- [k] ] ++
                  [ (1, genApp) ]
  where
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

genClosedType_ :: (Kind ()) -> Gen (Type TyName DefaultUni ())
genClosedType_ = runGenTm . genType

genTypeWithCtx :: Map TyName (Kind ()) -> (Kind ()) -> Gen (Type TyName DefaultUni ())
genTypeWithCtx ctx k = runGenTm $ local (\ e -> e { geTypes = ctx }) (genType k)

leKind :: (Kind ()) -> (Kind ()) -> Bool
leKind k1 k2 = go (reverse $ args k1) (reverse $ args k2)
  where
    args Type{}            = []
    args (KindArrow _ a b) = a : args b

    go [] _                = True
    go _ []                = False
    go (k : ks) (k' : ks')
      | leKind k k' = go ks ks'
      | otherwise   = go (k : ks) ks'

ltKind :: (Kind ()) -> (Kind ()) -> Bool
ltKind k k' = k /= k' && leKind k k'

substClosedType :: TyName -> (Type TyName DefaultUni ()) -> (Type TyName DefaultUni ()) -> (Type TyName DefaultUni ())
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

builtinKind :: SomeTypeIn DefaultUni -> Kind ()
builtinKind (SomeTypeIn t) = case t of
  DefaultUniProtoList -> Star :-> Star
  DefaultUniProtoPair -> Star :-> Star :-> Star
  DefaultUniApply f _ -> let _ :-> k = builtinKind (SomeTypeIn f) in k
  _                   -> Star

-- | Precondition: new kind is smaller or equal to old kind.
--   TODO (later): also allow changing which context it's valid in
fixKind :: HasCallStack
        => Map TyName (Kind ())
        -> Type TyName DefaultUni ()
        -> Kind ()
        -> Type TyName DefaultUni ()
fixKind ctx ty k
  | inferKind_ ctx ty == k = ty
  | not $ k `leKind` inferKind_ ctx ty =
      error "fixKind not smaller"
  | otherwise = case ty of
    TyVar _ _ | y : _ <- [ y | (y, k') <- Map.toList ctx, k == k' ] -> TyVar () y
              | otherwise -> minimalType k
    TyApp _ a b       -> TyApp () (fixKind ctx a $ KindArrow () (inferKind_ ctx b) k) b
    TyLam _ x kx b    ->
      case k of
        Type{}        -> fixKind ctx (substClosedType x (minimalType kx) b) k
        KindArrow _ ka kb
          | ka == kx  -> TyLam () x kx $ fixKind (Map.insert x kx ctx) b kb
          | not $ kb `leKind` kb' -> error "notgood"
          | otherwise -> TyLam () x ka $ fixKind ctx' b' kb
            where
              ctx' = Map.insert x ka ctx
              b'   = substClosedType x (minimalType kx) b
              kb'  = inferKind_ ctx' b'
    TyBuiltin{}       -> minimalType k
    _                 -> error "fixKind"

-- TODO: also shrink to new context
--       need old context and new context
shrinkKindAndType :: HasCallStack
                  => Map TyName (Kind ())
                  -> (Kind (), Type TyName DefaultUni ())
                  -> [(Kind (), Type TyName DefaultUni ())]
shrinkKindAndType ctx (k, ty) =
  [(k, m) | k <- k : shrink k, m <- [minimalType k], m /= ty] ++
  case ty of
    TyVar _ x         -> [(ky, TyVar () y) | (y, ky) <- Map.toList ctx, ltKind ky k || ky == k && y < x]
    TyFun _ a b       -> [(k, a), (k, b)] ++
                         [(k, TyFun () a b) | (_, a) <- shrinkKindAndType ctx (k, a)] ++
                         [(k, TyFun () a b) | (_, b) <- shrinkKindAndType ctx (k, b)]
    TyApp _ f a       -> [(ka, a) | ka `leKind` k] ++
                         [(k, b)                     | TyLam _ x _ b <- [f], not $ Set.member x (fvType b)] ++
                         [(k, substClosedType x a b) | TyLam _ x _ b <- [f], null (fvType a)] ++
                         concat [case kf' of
                                   Type{}              -> [(kf', f')]
                                   KindArrow _ ka' kb' -> [ (kb', TyApp () f' (fixKind ctx a ka'))
                                                          | leKind kb' k, leKind ka' ka]
                                 | (kf', f') <- shrinkKindAndType ctx (KindArrow () ka k, f)] ++
                         [(k, TyApp () (fixKind ctx f (KindArrow () ka' k)) a)
                         | (ka', a) <- shrinkKindAndType ctx (ka, a)]
      where ka = inferKind_ ctx a
    TyLam _ x ka b    -> [(KindArrow () ka' kb,  TyLam () x ka' $ substClosedType x (minimalType ka) b)
                         | ka' <- shrink ka] ++
                         [(KindArrow () ka  kb', TyLam () x ka b)
                         | (kb', b) <- shrinkKindAndType (Map.insert x ka ctx) (kb, b)]
      where KindArrow _ _ kb = k
    TyForall _ x ka b -> [(k, b) | not $ Set.member x (fvType b)] ++
                         [(k, TyForall () x ka' $ substClosedType x (minimalType ka) b) | ka' <- shrink ka] ++
                         [(k, TyForall () x ka b) | (_, b) <- shrinkKindAndType (Map.insert x ka ctx) (Star, b)]
    TyBuiltin{}       -> []
    TyIFix{}          -> error "shrinkKindAndType: TyIFix"

minimalType :: (Kind ()) -> (Type TyName DefaultUni ())
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

inferKind :: Map TyName (Kind ()) -> (Type TyName DefaultUni ()) -> Maybe (Kind ())
inferKind ctx ty = case ty of
  TyVar _ x        -> Map.lookup x ctx
  TyFun _ _ _      -> pure $ Star
  TyApp _ a _      -> do KindArrow _ _ k <- inferKind ctx a; pure k
  TyLam _ x k b    -> KindArrow () k <$> inferKind (Map.insert x k ctx) b
  TyForall _ _ _ _ -> pure $ Star
  TyBuiltin _ b    -> pure $ builtinKind b
  TyIFix{}         -> error "inferKind: TyIFix"

inferKind_ :: HasCallStack => Map TyName (Kind ()) -> (Type TyName DefaultUni ()) -> (Kind ())
inferKind_ ctx ty =
  case inferKind ctx ty of
    Nothing -> error "inferKind"
    Just k  -> k

shrinkType :: HasCallStack
           => Map TyName (Kind ())
           -> Type TyName DefaultUni ()
           -> [Type TyName DefaultUni ()]
shrinkType ctx ty = map snd $ shrinkKindAndType ctx (Star, ty)

shrinkTypeAtKind :: HasCallStack
                 => Map TyName (Kind ())
                 -> Kind ()
                 -> Type TyName DefaultUni ()
                 -> [Type TyName DefaultUni ()]
shrinkTypeAtKind ctx k ty = [ ty' | (k', ty') <- shrinkKindAndType ctx (k, ty), k == k' ]

substTypeCapturePar :: Map TyName (Type TyName DefaultUni ())
                    -> Type TyName DefaultUni ()
                    -> Type TyName DefaultUni ()
substTypeCapturePar sub ty = case ty of
    TyVar _ x        -> maybe ty id (Map.lookup x sub)
    TyFun _ a b      -> TyFun () (substTypeCapturePar sub a) (substTypeCapturePar sub b)
    TyApp _ a b      -> TyApp () (substTypeCapturePar sub a) (substTypeCapturePar sub b)
    TyLam _ x k b    -> TyLam () x k $ substTypeCapturePar sub b
    TyForall _ x k b -> TyForall () x k $ substTypeCapturePar sub b
    TyBuiltin{}      -> ty
    TyIFix{}         -> ty

data Polarity = Pos
              | Neg
              deriving (Ord, Eq, Show)

substType :: HasCallStack
          => Map TyName (Type TyName DefaultUni ())
          -> Type TyName DefaultUni ()
          -> Type TyName DefaultUni ()
substType = substType' True

substType' :: HasCallStack
           => Bool
           -> Map TyName (Type TyName DefaultUni ())
           -> Type TyName DefaultUni ()
           -> Type TyName DefaultUni ()
substType' nested sub ty0 = go fvs Set.empty sub ty0
  where
    fvs = Set.unions $ Map.keysSet sub : map fvType (Map.elems sub)

    go :: HasCallStack => _
    go fvs seen sub ty = case ty of
      TyVar _ x | Set.member x seen -> error "substType' loop"
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

renameType :: TyName -> TyName -> (Type TyName DefaultUni ()) -> (Type TyName DefaultUni ())
renameType x y | x == y    = id
               | otherwise = substType (Map.singleton x (TyVar () y))

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

checkKind :: Map TyName (Kind ()) -> (Type TyName DefaultUni ()) -> (Kind ()) -> Bool
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

fvTerm :: Term TyName Name DefaultUni DefaultFun ()
       -> Set Name
fvTerm tm = case tm of
  Let _ Rec binds body -> Set.unions
    (fvTerm body : [ fvTerm body | TermBind _ _ _ body <- toList binds ])
    `Set.difference` Map.keysSet (foldr addTmBind mempty binds)
  Let _ _ binds body   -> foldr go (fvTerm body) binds
    where go (TermBind _ _ (VarDecl _ x _) body) free = fvTerm body <> Set.delete x free
          go _ free                                   = free
  Var _ nm -> Set.singleton nm
  TyAbs _ _ _ t -> fvTerm t
  LamAbs _ x _ t -> Set.delete x (fvTerm t)
  Apply _ t t' -> fvTerm t <> fvTerm t'
  TyInst _ t _ -> fvTerm t
  Constant{} -> mempty
  Builtin{} -> mempty
  Error{} -> mempty
  IWrap{} -> error "fvTerm: IWrap"
  Unwrap{} -> error "fvTerm: Unwrap"

negativeVars :: Type TyName DefaultUni () -> Set TyName
negativeVars ty = case ty of
  TyFun _ a b      -> positiveVars a <> negativeVars b
  TyApp _ a b      -> negativeVars a <> negativeVars b
  TyLam _ x _ b    -> Set.delete x $ negativeVars b
  TyForall _ x _ b -> Set.delete x $ negativeVars b
  TyVar _ _        -> mempty
  TyBuiltin{}      -> mempty
  TyIFix{}         -> error "negativeVars: TyIFix"

positiveVars :: (Type TyName DefaultUni ()) -> Set TyName
positiveVars ty = case ty of
  TyFun _ a b      -> negativeVars a <> positiveVars b
  TyApp _ a b      -> positiveVars a <> positiveVars b
  TyLam _ x _ b    -> Set.delete x $ positiveVars b
  TyForall _ x _ b -> Set.delete x $ positiveVars b
  TyVar _ x        -> Set.singleton x
  TyBuiltin{}      -> mempty
  TyIFix{}         -> error "positiveVars: TyIFix"

genKindAndType :: Gen (Kind (), Type TyName DefaultUni ())
genKindAndType = do
  k <- arbitrary
  t <- genClosedType_ k
  return (k, t)

normalizeTy :: Type TyName DefaultUni () -> Type TyName DefaultUni ()
normalizeTy ty = case runQuoteT $ normalizeType ty of
  Left err               -> error "normalizeTy"
  Right (Normalized ty') -> ty'

unifyType :: Map TyName (Kind ())
          -> Set TyName
          -> Map TyName (Type TyName DefaultUni ())
          -> Type TyName DefaultUni ()
          -> Type TyName DefaultUni ()
          -> Maybe (Map TyName (Type TyName DefaultUni ()))
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

parSubstType :: Map TyName (Type TyName DefaultUni ())
             -> Type TyName DefaultUni ()
             -> (Type TyName DefaultUni ())
parSubstType = substType' False

genCtx :: Gen (Map TyName (Kind ()))
genCtx = do
  let m = 20
  n <- choose (0, m)
  let allTheVarsCalledX = [ TyName $ Name (fromString $ "x" ++ show i) (toEnum i) | i <- [1..m] ]
  shuf <- shuffle allTheVarsCalledX
  let xs = take n shuf
  ks <- vectorOf n arbitrary
  return $ Map.fromList $ zip xs ks

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

data TyInst = InstApp (Type TyName DefaultUni ()) | InstArg (Type TyName DefaultUni ())
  deriving stock Show

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

-- TODO TODO TODO
data Doc = TODODoc
  deriving stock Show
class Pretty a
instance Pretty a
pretty, text, (<+>), vcat :: a
pretty = error "TODO: pretty"
text = error "TODO: text"
(<+>) = error "TODO: (<+>)"
vcat = error "TODO: vcat"

ceDoc :: Testable t => Doc -> t -> Property
ceDoc d = counterexample (show d)

letCE :: (Pretty a, Testable p) => String -> a -> (a -> p) -> Property
letCE name x k = ceDoc (text name <+> "=" <+> pretty x) (k x)

forAllDoc :: (Pretty a, Testable p) => String -> Gen a -> (a -> [a]) -> (a -> p) -> Property
forAllDoc name g shr k = forAllShrinkBlind g shr $ \ x -> ceDoc (text name <+> "=" <+> pretty x) (k x)

notSoBad :: Pretty [a] => [a] -> Property
notSoBad []  = property True
notSoBad bad = ceDoc (pretty bad) False

prop_shrinkTypeSmaller :: Property
prop_shrinkTypeSmaller =
  forAllDoc "k,ty" genKindAndType (shrinkKindAndType Map.empty) $ \ (k, ty) ->
  notSoBad [ (k', ty') | (k', ty') <- shrinkKindAndType Map.empty (k, ty), not $ leKind k' k ]

prop_shrinkTypeSound :: Property
prop_shrinkTypeSound =
  forAllDoc "k,ty" genKindAndType (shrinkKindAndType Map.empty) $ \ (k, ty) ->
  checkKind Map.empty ty k ==>
  notSoBad [ (k, ty) | (k, ty) <- shrinkKindAndType Map.empty (k, ty), not $ checkKind Map.empty ty k ]

prop_genKindCorrect :: Property
prop_genKindCorrect =
  forAllDoc "ctx" genCtx (const []) $ \ ctx ->
  forAllDoc "k,ty" genKindAndType (shrinkKindAndType ctx) $ \ (k, ty) ->
  checkKind ctx ty k

prop_genSmallSize :: Property
prop_genSmallSize =
  forAllDoc "_,ty" genKindAndType (const []) $ \ (_, ty) ->
  letCE "size" (show $ typeSize ty) $ \ sz ->
    read (init $ drop (length @[] @Char "Size {unSize = ") sz) < (60 :: Int)

prop_shrinkKind :: Property
prop_shrinkKind =
  forAllDoc "k" arbitrary shrink $ \ k ->
  notSoBad [ k' | k' <- shrink k, not $ ltKind k' k ]

prop_fixKind :: Property
prop_fixKind =
  forAllDoc "k,ty" genKindAndType (shrinkKindAndType Map.empty) $ \ (k, ty) ->
  notSoBad [ (ty', k') | k' <- shrink k, let ty' = fixKind Map.empty ty k', not $ checkKind Map.empty ty' k' ]

-- Terms --
prop_unify :: Property
prop_unify =
  forAllDoc "n"   arbitrary shrink $ \ (NonNegative n) ->
  forAllDoc "m"   (choose (0, n)) shrink $ \ m ->
  letCE "xs" (take n allTheVarsCalledX) $ \ xs ->
  forAllDoc "ks" (vectorOf n arbitrary) (filter ((== n) . length) . shrink) $ \ ks ->
  letCE "ctx" (Map.fromList $ zip xs ks) $ \ ctx ->
  forAllDoc "ty1" (genTypeWithCtx ctx $ Star) (shrinkType ctx)  $ \ ty1 ->
  forAllDoc "ty2" (genTypeWithCtx ctx $ Star) (shrinkType ctx)  $ \ ty2 ->
  letCE "nty1" (normalizeTy ty1) $ \ _ ->
  letCE "nty2" (normalizeTy ty2) $ \ _ ->
  letCE "res" (unifyType ctx (Set.fromList $ take m xs) Map.empty ty1 ty2) $ \ res ->
  isJust res ==>
  let sub = fromJust res
      checkSub (x, ty) = letCE "x,ty" (x, ty)    $ \ _ ->
                         letCE "k" (ctx Map.! x) $ \ k -> checkKind ctx ty k
  in
  letCE "sty1" (substType sub ty1) $ \ sty1 ->
  letCE "sty2" (substType sub ty2) $ \ sty2 ->
  letCE "nsty1" (normalizeTy sty1) $ \ nsty1 ->
  letCE "nsty2" (normalizeTy sty2) $ \ nsty2 ->
  tabulate "sizes" [show $ min (Set.size $ fvType ty1) (Set.size $ fvType ty2)] $
  foldr (.&&.) (property $ nsty1 == nsty2) (map checkSub (Map.toList sub))
  where
    allTheVarsCalledX = [ TyName $ Name (fromString $ "x" ++ show i) (toEnum i) | i <- [1..] ]

prop_unifyRename :: Property
prop_unifyRename =
  forAllDoc "_, ty" genKindAndType (shrinkKindAndType mempty) $ \ (_, ty) ->
  letCE "rename ty" (either undefined id . runQuoteT $ rename ty) $ \ rnty ->
  isJust $ unifyType mempty mempty mempty ty rnty

prop_substType :: Property
prop_substType =
  forAllDoc "ctx" genCtx (const []) $ \ ctx ->
  forAllDoc "ty" (genTypeWithCtx ctx Star) (shrinkType ctx) $ \ ty ->
  forAllDoc "sub" (genSubst ctx) (shrinkSubst ctx) $ \ sub ->
  letCE "res" (substType sub ty) $ \ res ->
  fvTypeR sub ty == fvType res && checkKind ctx res Star
  where
    fvTypeR sub a = Set.unions $ ns : map (fvTypeR sub . (Map.!) sub) (Set.toList ss)
      where
          fvs = fvType a
          ss  = Set.intersection (Map.keysSet sub) fvs
          ns  = Set.difference fvs ss

genConstant :: SomeTypeIn DefaultUni -> GenTm (Term TyName Name DefaultUni DefaultFun ())
genConstant b = case b of
  SomeTypeIn DefaultUniBool    -> Const DefaultUniBool <$> liftGen arbitrary
  SomeTypeIn DefaultUniInteger -> Const DefaultUniInteger <$> liftGen arbitrary
  SomeTypeIn DefaultUniUnit    -> pure $ Const DefaultUniUnit ()
  SomeTypeIn DefaultUniString  -> Const DefaultUniString . fromString . getPrintableString <$> liftGen arbitrary
  _                            -> error "genConstant"

inhabitType :: (Type TyName DefaultUni ()) -> GenTm (Term TyName Name DefaultUni DefaultFun ())
inhabitType ty = local (\ e -> e { geTerms = mempty }) $ do
  help  <- asks geHelp
  fromJust <$> runMaybeT (findTm ty <|> (flip (TyInst ()) ty) <$> maybe mzero pure help
                                    <|> pure (Error () ty))
  where
    -- Do the obvious thing as long as target type is not type var
    -- When type var: magic (if higher-kinded type var: black magic)
    -- Ex: get `a` from D ts ==> get `a` from which ts, get which params from D
    findTm :: (Type TyName DefaultUni ()) -> MaybeT GenTm (Term TyName Name DefaultUni DefaultFun ())
    findTm (normalizeTy -> ty) = case ty of
      TyFun _ a b -> do
        x <- lift $ genFreshName "x"
        LamAbs () x a <$> mapMaybeT (bindTmName x a) (findTm b)
      TyForall _ x k b -> do
        TyAbs () x k <$> mapMaybeT (bindTyName x k) (findTm b)
      TyBuiltin _ b -> lift $ genConstant b
      (viewApp [] -> (f, _)) ->
        case f of
          TyVar () x  -> do
            _ <- asks geDatas
            asks (Map.lookup x . geDatas) >>= \ case
              Just dat -> foldr mplus mzero $ map (tryCon x ty) (constrTypes dat)
              Nothing  -> do
                vars <- asks geTerms
                ctx  <- asks geTypes
                let cands = Map.toList vars
                    doInst _ tm (InstApp instTy) = pure $ TyInst () tm instTy
                    doInst _ tm (InstArg argTy)  = Apply () tm <$> findTm argTy
                case [ local (\e -> e { geTerms = Map.delete x' (geTerms e) })
                       $ foldM (doInst n) (Var () x') insts
                     | (x', a)     <- cands,
                       n          <- [0..typeArity a],
                       Just insts <- [typeInstTerm ctx n ty a],
                       x `Set.notMember` fvArgs a
                     ] of
                  [] -> mzero
                  gs -> head gs
          _ -> mzero

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

    viewApp args (TyApp _ f x) = viewApp (x : args) f
    viewApp args ty            = (ty, args)

    fvArgs (TyForall _ x _ b) = Set.delete x (fvArgs b)
    fvArgs (TyFun _ a b)      = fvType a <> fvArgs b
    fvArgs _                  = mempty

typeArity :: Num a => Type tyname uni ann -> a
typeArity (TyForall _ _ _ a) = typeArity a
typeArity (TyFun _ _ b)      = 1 + typeArity b
typeArity _                  = 0

genAtomicTerm :: (Type TyName DefaultUni ()) -> GenTm (Term TyName Name DefaultUni DefaultFun ())
genAtomicTerm ty = do
  ctx  <- asks geTypes
  vars <- asks geTerms
  let unifyVar (x, xty) = typeInstTerm ctx 0 ty xty
                       <&> \ tys -> foldl (TyInst ()) (Var () x) [t | InstApp t <- tys]
  case catMaybes $ map unifyVar $ Map.toList vars of
    [] -> inhabitType ty
    gs -> liftGen $ elements gs

noEscape :: GenTm a -> GenTm a
noEscape = local $ \env -> env { geEscaping = NoEscape }

genTermOfType :: Type TyName DefaultUni ()
              -> GenTm (Term TyName Name DefaultUni DefaultFun ())
genTermOfType ty = snd <$> genTerm (Just ty)

genTerm :: Maybe (Type TyName DefaultUni ())
        -> GenTm (Type TyName DefaultUni (), Term TyName Name DefaultUni DefaultFun ())
genTerm mty = checkInvariant =<< do
  vars <- asks geTerms
  esc <- asks geEscaping
  let (letF, lamF, varAppF) = if Map.size vars < 20
                              then (30, 50, 10)
                              else (10, 30, 40)
      atomic | Just ty <- mty = (ty,) <$> genAtomicTerm ty
             | otherwise      = do ty <- genType Star; (ty,) <$> genAtomicTerm ty
  ifSizeZero atomic $
    frequencyTm $ [ (10, atomic) ] ++
                  [ (letF, genLet mty) ] ++
                  [ (30, genForall x k a) | Just (TyForall _ x k a) <- [mty] ] ++
                  [ (lamF, genLam a b) | Just (a, b) <- [funTypeView mty] ] ++
                  [ (varAppF, genVarApp mty) ] ++
                  [ (10, genApp mty) ] ++
                  [ (1, genError mty) ] ++
                  [ (10, genConst mty) | canConst mty ] ++
                  [ (1, genTerm . Just =<< genType Star) | isNothing mty ] ++
                  [ (10, genDatLet mty) | YesEscape <- [esc] ] ++
                  [ (10, genIfTrace) | isNothing mty ] ++
                  [ (10, genTraceLoc mty) ] ++
                  []
  where
    mkLoc :: String -> Int -> Int -> Int -> Int -> String
    mkLoc = error "TODO: mkLoc"

    checkInvariant p | not debug = pure p
    checkInvariant (ty, trm) = do
      tyctx <- asks geTypes
      trmctx <- asks geTerms
      -- Check that `mty` is well-scoped
      let unsMty = Set.mapMonotonic (nameUnique . unTyName) $ foldMap fvType mty
      uns <- getUniques
      when (not $ unsMty `Set.isSubsetOf` uns) $
        error"genTerm - scope"
      -- Check that trm :: ty
      help <- asks geHelp
      let trmctx' = case help of
            Just (Var _ helpVar) -> Map.insert helpVar helpType trmctx
            _                    -> trmctx
      case typeCheckTermInContext tyctx trmctx' trm ty of
        Right _  -> return (ty, trm)
        Left err -> error "genTerm - type"

    genTraceLoc mty = do
      (ty, tm) <- noEscape $ genTerm mty
      (_, loc) <- genLoc
      pure $ (ty, Apply () (Apply () (TyInst () BIF_Trace ty) loc) tm)

    genLoc = lift $ do
      sr <- choose (1,100)
      er <- choose (sr, 150)
      sc <- choose (1, 80)
      ec <- choose (sc, 120)
      pure ( TyBuiltin () (SomeTypeIn DefaultUniString)
           , Const DefaultUniString . Text.pack $ mkLoc "file" sr er sc ec)

    funTypeView Nothing                             = Just (Nothing, Nothing)
    funTypeView (Just (normalizeTy -> TyFun _ a b)) = Just (Just a, Just b)
    funTypeView _                                   = Nothing
    -- TODO: generate letrec
    -- TODO: generate datatype, term lets

    genIfTrace = do
      a <- genFreshTyName "a"
      let a' = TyVar () a
      liftGen $ elements [(TyForall () a Star $ TyBuiltin () (SomeTypeIn DefaultUniBool) ->> a' ->> a' ->> a', BIF_If)
                         ,(TyForall () a Star $ TyBuiltin () (SomeTypeIn DefaultUniString) ->> a' ->> a', BIF_Trace)]

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
      n   <- liftGen $ choose (1, 3)
      let vec :: GenTm a -> GenTm [a]
          vec = sequence . replicate n
      xs  <- genFreshNames $ replicate n "f"
      as  <- onSize (`div` 8) $ vec $ genType Star  -- TODO: generate something that matches the target type
      ss  <- vec $ liftGen $ elements [Strict, NonStrict]
      r   <- liftGen $ frequency [(5, pure True), (30, pure False)]
      let genBin (x, a) | r         = noEscape . bindTmName x a . genTermOfType $ a
                        | otherwise = noEscape . genTermOfType $ a
      sizeSplit_ 1 7 (mapM genBin (zip xs as)) (bindTmNames (zip xs as) $ genTerm mty) $ \ tms (ty, body) ->
        let mkBind (x, a, s) tm = TermBind () s
                                    (VarDecl () x a) tm
            b : bs = zipWith mkBind (zip3 xs as ss) tms
        in tms `deepseq` (ty, Let () (if r then Rec else NonRec) (b :| bs) body)

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
      let arity (TyForall _ _ _ b) = 1 + arity b
          arity (TyFun _ _ b)      = 1 + arity b
          arity _                  = 0

          appl :: HasCallStack => Int -> (Term TyName Name DefaultUni DefaultFun ()) -> _
          appl 0 tm b = return (b, tm)
          appl n tm (TyForall _ x k b) = do
            ty <- genType k
            x' <- genFreshTyName "x"
            appl (n - 1) (TyInst () tm ty) (substType (Map.singleton x' ty) $ renameType x x' b)
          appl n tm (TyFun _ a b) = do
            (_, arg) <- genTerm (Just a)
            appl (n - 1) (Apply () tm arg) b
          appl _ _ ty = error "appl"

          genV (x, ty0) = do
            let ty = normalizeTy ty0
            n <- liftGen $ choose (0, arity ty)
            onSize (`div` n) $ appl n (Var () x) ty
      asks (Map.toList . geTerms) >>= \ case
        []   -> do
          ty <- genType Star
          (ty,) <$> inhabitType ty
        vars -> liftGenF oneof $ map genV vars

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
        gs -> (ty,) <$> liftGenF oneof gs

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
    let dat = Datatype () (TyVarDecl () d k) [TyVarDecl () x k | (x, k) <- zip xs ks]
                       m
                       [ VarDecl () c (foldr (->>) dTy conArgs)
                       | (c, _conArgs) <- zip cs conArgss
                       , let conArgs = filter (Set.notMember d . negativeVars) _conArgs]
    bindDat dat $ cont dat

genDatatypeLets :: ([(Datatype TyName Name DefaultUni DefaultFun ())] -> GenTm a) -> GenTm a
genDatatypeLets cont = do
  n <- liftGen $ choose (0, 5 :: Int)
  let go 0 k = k []
      go n k = genDatatypeLet False $ \ dat -> go (n - 1) (k . (dat :))
  go n cont

shrinkClosedTypedTerm :: (Type TyName DefaultUni (), Term TyName Name DefaultUni DefaultFun ())
                      -> [(Type TyName DefaultUni (), Term TyName Name DefaultUni DefaultFun ())]
shrinkClosedTypedTerm (ty, LamAbs _ help helpType tm) =
  map (second $ LamAbs () help helpType) $ shrinkTypedTerm Map.empty (Map.singleton help helpType) (ty, tm)
shrinkClosedTypedTerm p = shrinkTypedTerm mempty mempty p

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

    isLoc (LIT_Loc _) = True
    isLoc _           = False

    go :: HasCallStack => _
    go tyctx ctx (ty, tm) =
      filter (\ (ty, tm) -> not (isLoc tm) && scopeCheckTyVars tyctx (ty, tm)) $
      nonstructural tyctx ctx (ty, tm) ++
      structural    tyctx ctx (ty, tm)

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

        Apply _ fun arg | Right argTy <- inferTypeInContext tyctx ctx arg ->
          [(argTy, arg), (TyFun () argTy ty, fun)] ++
          go tyctx ctx (TyFun () argTy ty, fun) ++
          go tyctx ctx (argTy, arg)

        TyAbs _ x _ body ->
          [ fixupTerm_ (Map.insert x k tyctx) ctx tyctx ctx tyInner' body
          | TyForall _ y k tyInner <- [ty]
          , let tyInner' = substClosedType y (minimalType k) tyInner
          ]

        Const DefaultUniBool _ ->
          [ (TyBuiltin () (SomeTypeIn DefaultUniUnit), Const DefaultUniUnit ()) ]

        Const DefaultUniInteger _ ->
          [ (TyBuiltin () (SomeTypeIn DefaultUniUnit), Const DefaultUniUnit ()) ]

        Const DefaultUniString _ ->
          [ (TyBuiltin () (SomeTypeIn DefaultUniUnit), Const DefaultUniUnit ()) ]

        Const b _ -> [ (TyBuiltin () (SomeTypeIn b), bin) | bin <- [ minimalBuiltin (SomeTypeIn b) ]
                                                          , bin /= tm ]

        _ -> []

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
          ] where Right (TyForall _ x k tyInner) = inferTypeInContext tyctx ctx fun

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
          | Right argTy <- [inferTypeInContext tyctx ctx arg]
          , (TyFun _ argTy' ty', fun') <- go tyctx ctx (TyFun () argTy ty, fun)
          , let arg' = fixupTerm tyctx ctx tyctx ctx argTy' arg
          ] ++
          [ (ty,  Apply () fun' arg')
          | Right argTy <- [inferTypeInContext tyctx ctx arg]
          , (argTy', arg') <- go tyctx ctx (argTy, arg)
          , let fun' = fixupTerm tyctx ctx tyctx ctx (TyFun () argTy' ty) fun
          ]

        Const DefaultUniBool b ->
          [ (ty, Const DefaultUniBool b') | b' <- shrink b ]

        Const DefaultUniInteger i ->
          [ (ty, Const DefaultUniInteger i') | i' <- shrink i ]

        _ -> []

inferTypeInContext :: Map TyName (Kind ())
                   -> Map Name (Type TyName DefaultUni ())
                   -> Term TyName Name DefaultUni DefaultFun ()
                   -> Either Doc (Type TyName DefaultUni ())
inferTypeInContext tyctx ctx tm = either (Left . text . show) (Right . id)
                                $ runQuoteT @(Either (Error DefaultUni DefaultFun ())) $ do
  cfg <- getDefTypeCheckConfig ()
  Normalized _ty' <- runQuoteT $ inferType cfg tm'
  let ty' = substEscape Pos (Map.keysSet esc <> foldr (<>) (fvType _ty') (fvType <$> esc)) esc _ty' -- yuck
  return $ stripFuns tms $ stripForalls mempty tys ty'
  where
    tm' = addTyLams tys $ addLams tms tm
    rntm = case runQuoteT $ rename tm' of
      Left _     -> error "impossible"
      Right tm'' -> tm''
    -- Note, we don't need to run `escapingSubst` here because we are
    -- not generating type synonyms
    esc = Map.fromList (zip dats' $ map (TyVar ()) dats)

    dats = map fst $ datatypes tm'
    dats' = map fst $ datatypes rntm

    tys = Map.toList tyctx
    tms = Map.toList ctx

    addTyLams [] tm            = tm
    addTyLams ((x, k) : xs) tm = TyAbs () x k $ addTyLams xs tm

    addLams [] tm             = tm
    addLams ((x, ty) : xs) tm = LamAbs () x ty $ addLams xs tm

    stripForalls sub [] ty                            = parSubstType sub ty
    stripForalls sub ((x, _) : xs) (TyForall _ y _ b) = stripForalls (Map.insert y (TyVar () x) sub) xs b
    stripForalls _ xs ty                              = error "stripForalls"

    stripFuns [] ty                  = ty
    stripFuns (_ : xs) (TyFun _ _ b) = stripFuns xs b
    stripFuns xs ty                  = error "stripFuns"

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

fixupTerm_ :: Map TyName (Kind ())
           -> Map Name (Type TyName DefaultUni ())
           -> Map TyName (Kind ())
           -> Map Name (Type TyName DefaultUni ())
           -> Type TyName DefaultUni ()
           -> Term TyName Name DefaultUni DefaultFun ()
           -> (Type TyName DefaultUni (), Term TyName Name DefaultUni DefaultFun ())
fixupTerm_ tyctxOld ctxOld tyctxNew ctxNew tyNew tm =
  case inferTypeInContext tyctxNew ctxNew tm of
    Left{}   -> case tm of
      LamAbs _ x a tm | TyFun () _ b <- tyNew -> (a ->>) *** (LamAbs () x a)
                                              $ fixupTerm_ tyctxOld (Map.insert x a ctxOld)
                                                           tyctxNew (Map.insert x a ctxNew) b tm
      Apply _ (Apply _ (TyInst _ BIF_Trace _) s) tm ->
        let (ty', tm') = fixupTerm_ tyctxOld ctxOld tyctxNew ctxNew tyNew tm
        in (ty', Apply () (Apply () (TyInst () BIF_Trace ty') s) tm')
      _ | TyBuiltin _ b <- tyNew -> (tyNew, minimalBuiltin b)
        | otherwise -> (tyNew, mkHelp ctxNew tyNew)
    Right ty -> (ty, tm)

fixupTerm :: Map TyName (Kind ())
          -> Map Name (Type TyName DefaultUni ())
          -> Map TyName (Kind ())
          -> Map Name (Type TyName DefaultUni ())
          -> Type TyName DefaultUni ()
          -> Term TyName Name DefaultUni DefaultFun ()
          -> Term TyName Name DefaultUni DefaultFun ()
fixupTerm _ _ tyctxNew ctxNew tyNew tm
  | isRight (typeCheckTermInContext tyctxNew ctxNew tm tyNew) = tm
  | otherwise                                                 = mkHelp ctxNew tyNew

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
    TermBind _ s (VarDecl _ x ty) tm -> [ TermBind () s (VarDecl () x ty') tm'
                                        | (ty', tm') <- shrinkTypedTerm tyctx ctx (ty, tm)
                                        ] ++
                                        [ TermBind () Strict (VarDecl () x ty) tm | s == NonStrict ]
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

helpType :: Type TyName DefaultUni ()
helpType = TyForall () a Star (TyVar () a)
  where a = tyvar "a" 0

genTypeAndTerm_ :: Gen (Type TyName DefaultUni (), Term TyName Name DefaultUni DefaultFun ())
genTypeAndTerm_ = runGenTm $ do
    (ty, body)    <- genTerm Nothing
    ~(Just (Var _ help)) <- asks geHelp
    return (ty, LamAbs () help helpType body)

genTypeAndTermNoHelp_ :: Gen (Type TyName DefaultUni (), Term TyName Name DefaultUni DefaultFun ())
genTypeAndTermNoHelp_ = runGenTm $ local (\ e -> e { geHelp = Nothing }) $ genTerm Nothing

genFullyApplied :: Type TyName DefaultUni ()
                -> Term TyName Name DefaultUni DefaultFun ()
                -> Gen (Type TyName DefaultUni (), Term TyName Name DefaultUni DefaultFun ())
genFullyApplied typ trm = runGenTm $ local (\ e -> e { geHelp = Nothing }) $ go trm
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

genTermInContext_ :: Map TyName (Kind ())
                  -> Map Name (Type TyName DefaultUni ())
                  -> Type TyName DefaultUni ()
                  -> Gen (Term TyName Name DefaultUni DefaultFun ())
genTermInContext_ tyctx ctx ty =
  runGenTm $ local (\ e -> e { geTypes = tyctx, geTerms = ctx, geEscaping = NoEscape }) $
    snd <$> genTerm (Just ty)

prop_typeInstHelp :: Property
prop_typeInstHelp =
  forAllDoc "ctx" genCtx (const []) $ \ ctx ->
  forAllDoc "ty" (genTypeWithCtx ctx $ Star) (shrinkType ctx) $ \ ty ->
  isJust $ typeInstTerm ctx 0 ty helpType

prop_typeInstTerm :: Property
prop_typeInstTerm =
  forAllDoc "ctx"    genCtx                      (const [])       $ \ ctx ->
  forAllDoc "ty"     (genTypeWithCtx ctx $ Star) (shrinkType ctx) $ \ ty ->
  forAllDoc "target" (genTypeWithCtx ctx $ Star) (shrinkType ctx) $ \ target ->
  doTypeInstTermCheck ctx ty target

doTypeInstTermCheck :: Map TyName (Kind ())
                    -> Type TyName DefaultUni ()
                    -> Type TyName DefaultUni ()
                    -> Property
doTypeInstTermCheck ctx ty target =
  case [ ((n, insts), err)
       | n <- [0..arity ty+3],
         Just insts <- [typeInstTerm ctx n target ty],
         Left err <- [checkInst ctx x ty insts target]
       ] of
    []  -> property True
    bad -> ceDoc (pretty bad) False
  where
    x = Name "x" (toEnum 0)
    arity (TyForall _ _ _ a) = arity a
    arity (TyFun _ _ b)      = 1 + arity b
    arity _                  = 0

    checkInst ctx x ty insts target = typeCheckTermInContext ctx tmCtx tm target
      where
        (tmCtx, tm) = go (toEnum 1) (Map.singleton x ty) (Var () x) insts
        go _ tmCtx tm [] = (tmCtx, tm)
        go i tmCtx tm (InstApp ty : insts) = go i tmCtx (TyInst () tm ty) insts
        go i tmCtx tm (InstArg ty : insts) = go (succ i) (Map.insert y ty tmCtx) (Apply () tm (Var () y)) insts
          where y = Name "y" i

prop_genTypeCorrect :: Property
prop_genTypeCorrect =
  forAllDoc "ty,tm"   genTypeAndTerm_ (const [])   $ \ (ty, tm) ->
  case typeCheckTerm tm (TyFun () helpType ty) of
    Left err -> counterexample (show err) False
    Right () -> property True

prop_genTypeCorrectFullyApplied :: Property
prop_genTypeCorrectFullyApplied =
  forAllDoc "ty,tm"   genTypeAndTerm_ (const []) $ \ (ty, tm) ->
  case typeCheckTerm tm (TyFun () helpType ty) of
    Left err -> counterexample (show err) False
    Right () -> property True

prop_shrinkTermSound :: Property
prop_shrinkTermSound =
  forAllShrinkBlind (pure False) (\ sh -> [ True | not sh ]) $ \ _ ->
  forAllDoc "ty,tm"   genTypeAndTerm_ shrinkClosedTypedTerm $ \ (ty, tm) ->
  let shrinks = shrinkClosedTypedTerm (ty, tm) in
  isRight (typeCheckTerm tm $ TyFun () helpType ty) ==>
  not (null shrinks) ==>
  notSoBad [ (ty, tm, (err, scopeCheckTyVars Map.empty (ty, tm)))
           | (ty, tm) <- shrinks, Left err <- [typeCheckTerm tm (TyFun () helpType ty)] ]

shrinkRNF :: NFData a => Int -> (a -> [a]) -> a -> [a]
shrinkRNF timeLimitMicroseconds shrinker a =
  catMaybes [ unsafePerformIO $ timeout timeLimitMicroseconds (rnf a' `seq` pure a') | a' <- shrinker a ]

prop_canShrinkTerm :: Property
prop_canShrinkTerm =
  let second = 1000000 in
  forAllDoc "ty,tm" genTypeAndTerm_ (shrinkRNF second shrinkClosedTypedTerm)   $ \ (ty, tm) ->
  let ss = shrinkClosedTypedTerm (ty, tm) in
  foldr (.&&.)
    (counterexample "Can't count number of shrinks" $ within (10*second) (length ss `seq` property True))
    [ within second (rnf s `seq` True) | s <- ss]

prop_genWellTypedFullyApplied :: Property
prop_genWellTypedFullyApplied =
  forAllDoc "ty, tm" genTypeAndTermNoHelp_ (shrinkTypedTerm mempty mempty) $ \ (ty, tm) ->
  forAllDoc "ty', tm'" (genFullyApplied ty tm) (const []) $ \ (ty', tm') ->
    case typeCheckTerm tm' ty' of
      Right _  -> property True
      Left err -> ceDoc err False

prop_varsStats :: Property
prop_varsStats =
  forAllDoc "_,tm"      genTypeAndTerm_ shrinkClosedTypedTerm     $ \ (_, tm) ->
  tabulate "vars" (map (filter isAlpha . show . pretty @(_ -> Doc)) $ vars tm) $ property True
  where
    vars (Var _ x)        = [x]
    vars (TyInst _ a _)   = vars a
    vars (Let _ _ _ b)    = vars b
    vars (LamAbs _ _ _ b) = vars b
    vars (Apply _ a b)    = vars a ++ vars b
    vars Error{}          = [Name "error" $ toEnum 0]
    vars _                = []

prop_inhabited :: Property
prop_inhabited =
  forAllDoc "ty,tm" (genInhab mempty) (shrinkTypedTerm mempty mempty) $ \ (ty, tm) ->
      case typeCheckTerm tm ty of
        Right _  -> property True
        Left doc -> ceDoc doc False
  where
    genInhab ctx = runGenTm $ local (\ e -> e { geTypes = ctx, geHelp = Nothing }) $
      genDatatypeLets $ \ dats -> do
        ty <- genType Star
        tm <- inhabitType ty
        return (ty, foldr (\ dat -> Let () NonRec (DatatypeBind () dat :| [])) tm dats)

prop_numShrink :: Property
prop_numShrink = forAllDoc "ty,tm"   genTypeAndTerm_ (const []) $ \ (ty, tm) ->
  let shrinks = shrinkClosedTypedTerm (ty, tm)
      n = fromIntegral (length shrinks)
      u = fromIntegral (length $ nub shrinks)
      r | n > 0     = (n - u) / n :: Double
        | otherwise = 0
  in
  tabulate "r" [printf "%0.1f" r] True

-- TODO: we want this property somewhere!
-- compile :: Term TyName Name DefaultUni DefaultFun ()
--         -> Either (CompileError DefaultUni DefaultFun) (CompiledCode a)
-- compile _tm = either Left Right $ runQuoteT $ do
--   -- Make sure that names are unique (that's not guaranteed by QuickCheck)
--   tm <- rename _tm
--   plcTcConfig <- PLC.getDefTypeCheckConfig PIR.noProvenance
--   let hints = UPLC.InlineHints $ \a _ -> case a of
--                 PIR.DatatypeComponent PIR.Destructor _ -> True
--                 _                                      -> False
--       pirCtx = PIR.toDefaultCompilationCtx plcTcConfig
--              & set (PIR.ccOpts . PIR.coOptimize) True
--              & set (PIR.ccOpts . PIR.coPedantic) False
--              & set (PIR.ccOpts . PIR.coVerbose) False
--              & set (PIR.ccOpts . PIR.coDebug) False
--              & set (PIR.ccOpts . PIR.coMaxSimplifierIterations)
--                       (PIR.defaultCompilationOpts ^. PIR.coMaxSimplifierIterations)
--              & set PIR.ccTypeCheckConfig Nothing
--       uplcSimplOpts = UPLC.defaultSimplifyOpts
--             & set UPLC.soMaxSimplifierIterations (PIR.defaultCompilationOpts ^. PIR.coMaxSimplifierIterations)
--             & set UPLC.soInlineHints hints
--
--   plcT <- flip runReaderT pirCtx $ PIR.compileReadableToPlc $ fmap Original tm
--   plcTcError <- runExceptT @(PLC.Error _ _ _)
--              $ UPLC.deBruijnTerm =<< UPLC.simplifyTerm uplcSimplOpts (UPLC.erase plcT)
--   case plcTcError of
--     Left _   -> error "wrong"
--     Right cc -> return $ DeserializedCode (UPLC.Program () (PLC.defaultVersion ()) $ void cc) Nothing mempty
--
-- prop_compile :: Property
-- prop_compile =
--   forAllDoc "_,tm" genTypeAndTermNoHelp_ (shrinkTypedTerm mempty mempty) $ \ (_, tm) ->
--   isRight $ compile tm

within' :: NFData a => Int -> a -> Bool
within' t a = isJust $ unsafePerformIO $ timeout t (a `deepseq` pure a)

letCE' :: (Pretty a, NFData a, Testable p) => Int -> String -> a -> (a -> p) -> Property
letCE' timeout name tm cont =
  within' timeout tm ==>
    letCE name tm cont

typeCheckTerm :: Term TyName Name DefaultUni DefaultFun ()
              -> Type TyName DefaultUni ()
              -> Either Doc ()
typeCheckTerm = typeCheckTermInContext Map.empty Map.empty

-- TODO: we probably need tests for this now that
-- it's more complicated than before...
--
-- It's also not clear that this is the only way of doing this...
typeCheckTermInContext :: Map TyName (Kind ())
                       -> Map Name (Type TyName DefaultUni ())
                       -> Term TyName Name DefaultUni DefaultFun ()
                       -> Type TyName DefaultUni ()
                       -> Either Doc ()
typeCheckTermInContext tyctx ctx tm ty = do
    ty' <- inferTypeInContext tyctx ctx tm
    unless (isJust $ unifyType tyctx mempty mempty ty' ty) . Left $
      "Types don't match" <+> vcat [ "tyctx =" <+> pretty tyctx
                                    , "ctx =" <+> pretty ctx
                                    , "tm =" <+> pretty tm
                                    , "ty =" <+> pretty ty
                                    , "normalizeTy ty =" <+> pretty (normalizeTy ty)
                                    , "ty' =" <+> pretty ty'
                                    , "normalizeTy ty' =" <+> pretty (normalizeTy ty')]

escapingSubst :: (Term TyName Name DefaultUni DefaultFun ()) -> Map TyName (Type TyName DefaultUni ())
escapingSubst tm = case tm of
  Var _ _           -> mempty
  Builtin _ _       -> mempty
  Constant _ _      -> mempty
  Apply _ tm _      -> escapingSubst tm
  LamAbs _ _ _ tm'  -> escapingSubst tm'
  TyAbs _ _ _ tm'   -> escapingSubst tm'
  TyInst _ tm' _    -> escapingSubst tm'
  Let _ _ binds tm' -> foldr addTyBindSubst (escapingSubst tm') binds
    where
      addTyBindSubst (TypeBind _ (TyVarDecl _ a _) ty) = Map.insert a ty
      addTyBindSubst _                                 = id
  Error _ _ -> mempty
  _ -> error "IFix very bad no no no"


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

fvTypeR :: Map TyName (Type TyName DefaultUni ()) -> (Type TyName DefaultUni ()) -> Set TyName
fvTypeR sub a = Set.unions $ ns : map (fvTypeR sub . (Map.!) sub) (Set.toList ss)
      where
          fvs = fvType a
          ss  = Set.intersection (Map.keysSet sub) fvs
          ns  = Set.difference fvs ss

-- Container

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

deriving stock instance Eq (Term TyName Name DefaultUni DefaultFun ())
deriving stock instance Eq (Binding TyName Name DefaultUni DefaultFun ())
deriving stock instance Eq (VarDecl TyName Name DefaultUni DefaultFun ())
deriving stock instance Eq (TyVarDecl TyName ())
deriving stock instance Eq (Datatype TyName Name DefaultUni DefaultFun ())

deriving instance NFData (Term TyName Name DefaultUni DefaultFun ())
deriving instance NFData (Binding TyName Name DefaultUni DefaultFun ())
deriving instance NFData (VarDecl TyName Name DefaultUni DefaultFun ())
deriving instance NFData (TyVarDecl TyName ())
deriving instance NFData (Datatype TyName Name DefaultUni DefaultFun ())
deriving instance NFData Strictness
deriving instance NFData Recursivity
