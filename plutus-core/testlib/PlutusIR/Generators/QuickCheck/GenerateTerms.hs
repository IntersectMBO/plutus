-- editorconfig-checker-disable-file
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ViewPatterns #-}
{-# OPTIONS_GHC -Wno-incomplete-uni-patterns #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}
{-# OPTIONS_GHC -Wno-partial-type-signatures #-}

module PlutusIR.Generators.QuickCheck.GenerateTerms where

import PlutusIR.Generators.QuickCheck.Common

import PlutusCore.Generators.QuickCheck.Builtin
import PlutusCore.Generators.QuickCheck.Common
import PlutusCore.Generators.QuickCheck.GenTm
import PlutusCore.Generators.QuickCheck.GenerateTypes
import PlutusCore.Generators.QuickCheck.ShrinkTypes
import PlutusCore.Generators.QuickCheck.Substitutions
import PlutusCore.Generators.QuickCheck.Unification
import PlutusCore.Generators.QuickCheck.Utils

import PlutusCore.Builtin
import PlutusCore.Core (argsFunKind)
import PlutusCore.Default
import PlutusCore.MkPlc (mkConstantOf)
import PlutusCore.Name.Unique
import PlutusCore.Pretty
import PlutusCore.Subst (typeSubstClosedType)
import PlutusIR
import PlutusIR.Compiler
import PlutusIR.Subst

import Control.Lens ((<&>))
import Control.Monad
import Control.Monad.Except
import Control.Monad.Reader
import Data.Bifunctor
import Data.Default.Class
import Data.Either
import Data.List.NonEmpty (NonEmpty (..))
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Maybe
import Data.Proxy
import Data.Set qualified as Set
import Data.Set.Lens (setOf)
import Data.String
import GHC.Stack
import Prettyprinter

{-| This type keeps track of what kind of argument, term argument (`InstArg`) or
type argument (`InstApp`) is required for a function. This type is used primarily
with `findInstantiation` below where we do unification to figure out if we can
use a variable to construct a term of a target type. -}
data TyInst = InstApp (Type TyName DefaultUni ()) | InstArg (Type TyName DefaultUni ())
  deriving stock (Show)

instance PrettyBy config (Type TyName DefaultUni ()) => PrettyBy config TyInst where
  prettyBy ctx (InstApp ty) = prettyBy ctx ty
  prettyBy ctx (InstArg ty) = brackets (prettyBy ctx ty)

{-| If successful `findInstantiation n target ty` for an `x :: ty` gives a sequence of `TyInst`s containing `n`
  `InstArg`s such that `x` instantiated (type application for `InstApp` and applied to a term of
  the given type for `InstArg`) at the `TyInsts`s has type `target` -}
findInstantiation
  :: HasCallStack
  => TypeCtx
  -> Int
  -> Type TyName DefaultUni ()
  -> Type TyName DefaultUni ()
  -> Either String [TyInst]
findInstantiation ctx n target ty = do
  sub <- unifyType (ctx <> ctx') flex target b
  let
    -- We map any unsolved flexible variable to a 'minimalType'.
    defaultSub = minimalType <$> ctx'
    doSub :: HasCallStack => _
    doSub = substType defaultSub . substType sub
    doSubI (InstApp t) = InstApp (doSub t)
    doSubI (InstArg t) = InstArg (doSub t)
  pure $ map doSubI insts
  where
    fvs = setOf ftvTy target <> setOf ftvTy ty <> Map.keysSet ctx
    (ctx', flex, insts, b) = view Map.empty Set.empty [] n fvs ty

    -- TODO: documentation!
    view ctx' flex insts n fvs (TyForall _ x k b) =
      view
        (Map.insert x' k ctx')
        (Set.insert x' flex)
        (InstApp (TyVar () x') : insts)
        n
        (Set.insert x' fvs)
        b'
      where
        (x', b')
          | Set.member x fvs = let x' = freshenTyNameWith fvs x in (x', renameVar x x' b)
          | otherwise = (x, b)
    view ctx' flex insts n fvs (TyFun _ a b) | n > 0 = view ctx' flex (InstArg a : insts) (n - 1) fvs b
    view ctx' flex insts _ _ a = (ctx', flex, reverse insts, a)

genConstant :: SomeTypeIn DefaultUni -> GenTm (Term TyName Name DefaultUni DefaultFun ())
genConstant (SomeTypeIn b) = case toSingKind b of
  SingType -> mkConstantOf () b <$> bring (Proxy @ArbitraryBuiltin) b (liftGen arbitraryBuiltin)
  _ -> error "Higher-kinded built-in types cannot be used here"

{-| Try to inhabit a given type in as simple a way as possible,
prefers to not default to `error` -}
inhabitType :: Type TyName DefaultUni () -> GenTm (Term TyName Name DefaultUni DefaultFun ())
inhabitType ty0 = local (\e -> e {geTerms = mempty}) $ do
  errOrRes <- runExceptT $ findTm ty0
  pure $ case errOrRes of
    Left _ -> Error () ty0
    Right res -> res
  where
    -- Do the obvious thing as long as target type is not type var
    -- When type var: magic (if higher-kinded type var: black magic)
    -- Ex: get `a` from D ts ==> get `a` from which ts, get which params from D
    -- This function does not fail to error.
    --
    -- NOTE: because we make recursive calls to findTm in this function instead of
    -- inhabitType we don't risk generating terms that are "mostly ok but something is error",
    -- this function will avoid error if possible.
    findTm
      :: Type TyName DefaultUni ()
      -> ExceptT String GenTm (Term TyName Name DefaultUni DefaultFun ())
    findTm (normalizeTy -> ty) = case ty of
      TyFun _ a b -> do
        x <- lift $ genLikelyFreshName "x"
        LamAbs () x a <$> mapExceptT (bindTmName x a) (findTm b)
      TyForall _ x k b -> do
        TyAbs () x k <$> mapExceptT (bindTyName x k) (findTm b)
      TyBuiltin _ someUni -> lift $ genConstant someUni
      -- If we have a type-function application
      (viewApp [] -> (f, _)) ->
        case f of
          TyVar () x -> do
            _ <- asks geDatas
            asks (Map.lookup x . geDatas) >>= \case
              -- If the head is a datatype try to inhabit one of its constructors
              Just dat -> foldr mplus mzero $ map (tryCon x ty) (constrTypes dat)
              -- If its not a datatype we try to use whatever bound variables
              -- we have to inhabit the type
              Nothing -> do
                vars <- asks geTerms
                ctx <- asks geTypes
                let cands = Map.toList vars
                    -- If we are instantiating something simply instantiate every
                    -- type application with type required by findInstantiation
                    doInst _ tm (InstApp instTy) = pure $ TyInst () tm instTy
                    -- If we instantiate an application, only succeed if we find
                    -- a non-error argument.
                    doInst _ tm (InstArg argTy) = Apply () tm <$> findTm argTy
                -- Go over every type and try to inhabit the type at the arguments
                case [ local (\e -> e {geTerms = Map.delete x' (geTerms e)}) $
                         foldM (doInst n) (Var () x') insts
                     | (x', a) <- cands
                     , n <- [0 .. typeArity a]
                     , Right insts <- [findInstantiation ctx n ty a]
                     , x `Set.notMember` fvArgs a
                     ] of
                  [] -> mzero
                  g : _ -> g
          _ -> mzero

    -- Try to inhabit a constructor `con` of type `conTy` in datatype `d` at type `ty`
    tryCon d ty1 (con, conTy)
      | Set.member d (fvArgs conTy) = mzero -- <- This is ok, since no mutual recursion
      | otherwise = do
          -- Check that we haven't banned this constructor
          tmctx <- lift $ asks geTerms
          if Map.lookup con tmctx == Just conTy
            then do
              tyctx <- lift $ asks geTypes
              insts0 <- liftEither $ findInstantiation tyctx (typeArity conTy) ty1 conTy
              let go tm [] = return tm
                  go tm (InstApp ty : insts) = go (TyInst () tm ty) insts
                  go tm (InstArg ty : insts) = do
                    arg <- findTm ty
                    go (Apply () tm arg) insts
              go (Var () con) insts0
            else mzero

    -- CODE REVIEW: wouldn't it be neat if this existed somewhere?
    viewApp args (TyApp _ f x) = viewApp (x : args) f
    viewApp args ty = (ty, args)

    -- Get the free variables that appear in arguments of a mixed arrow-forall type
    fvArgs (TyForall _ x _ b) = Set.delete x (fvArgs b)
    fvArgs (TyFun _ a b) = setOf ftvTy a <> fvArgs b
    fvArgs _ = mempty

-- CODE REVIEW: does this exist anywhere?
typeArity :: Num a => Type tyname uni ann -> a
typeArity (TyForall _ _ _ a) = typeArity a
typeArity (TyFun _ _ b) = 1 + typeArity b
typeArity _ = 0

-- | Generate as small a term as possible to match a given type.
genAtomicTerm :: Type TyName DefaultUni () -> GenTm (Term TyName Name DefaultUni DefaultFun ())
genAtomicTerm ty = do
  ctx <- asks geTypes
  vars <- asks geTerms
  -- First try cheap unification
  let unifyVar (x, xty) =
        findInstantiation ctx 0 ty xty
          <&> \tys -> foldl (TyInst ()) (Var () x) [t | InstApp t <- tys]
  case rights $ map unifyVar $ Map.toList vars of
    -- If unification didn't work try the heavy-handed `inhabitType`.
    -- NOTE: We could probably just replace this whole function with
    -- `inhabitType` and the generators would run fine, but this method
    -- is probably faster a lot of the time and doesn't rely on the
    -- order that thins are chosen `inhabitType`. It is also going to generate
    -- a more even distribution than `inhabitType` (which for performance reasons
    -- always returns the first thing it finds).
    [] -> inhabitType ty
    gs -> liftGen $ elements gs

{-| Generate a term of a given type.

Requires the type to be of kind *. -}
genTermOfType
  :: Type TyName DefaultUni ()
  -> GenTm (Term TyName Name DefaultUni DefaultFun ())
genTermOfType ty = snd <$> genTerm (Just ty)

{-| Generate a term, if the first argument is Nothing then we get something of any type
and if the first argument is `Just ty` we get something of type `ty`.

Requires the type to be of kind *. -}
genTerm
  :: Maybe (Type TyName DefaultUni ())
  -> GenTm (Type TyName DefaultUni (), Term TyName Name DefaultUni DefaultFun ())
genTerm mty = checkInvariants $ do
  customF <- asks geCustomFreq
  customG <- asks geCustomGen
  vars <- asks geTerms
  esc <- asks geEscaping
  -- Prefer to generate things that bind variables until we have "enough" (20...)
  let (letF, lamF, varAppF) =
        if Map.size vars < 20
          then (30, 50, 10)
          else (10, 30, 40)
      atomic
        | Just ty <- mty = (ty,) <$> genAtomicTerm ty
        | otherwise = do
            ty <- genType $ Type ()
            (ty,) <$> genAtomicTerm ty
  ifAstSizeZero atomic $
    frequency $
      [(10, atomic)]
        ++ [(letF, genLet mty)]
        ++ [(30, genForall x k a) | Just (TyForall _ x k a) <- [mty]]
        ++ [(lamF, genLam a b) | Just (a, b) <- [funTypeView mty]]
        ++ [(varAppF, genVarApp mty)]
        ++ [(10, genApp mty)]
        ++ [(1, genError mty)]
        ++ [(10, genConst mty) | canConst mty]
        ++ [(10, genDatLet mty) | YesEscape <- [esc]]
        ++ [(10, genIfTrace) | isNothing mty]
        ++ [(customF, customG mty)]
  where
    checkInvariants gen = do
      (ty, tm) <- gen
      debug <- asks geDebug
      tyctx <- asks geTypes
      tmctx <- asks geTerms
      if debug
        then case typeCheckTermInContext tyctx tmctx tm ty of
          Left err ->
            ( error . show $
                "genTerm - checkInvariants: term "
                  <> prettyReadable tm
                  <> " does not type check at type "
                  <> prettyReadable ty
                  <> " in type context "
                  <> prettyReadable tyctx
                  <> " and term context "
                  <> prettyReadable tmctx
                  <> " with error message "
                  <> fromString err
            )
          _ -> return (ty, tm)
        else
          return (ty, tm)

    funTypeView Nothing = Just (Nothing, Nothing)
    funTypeView (Just (normalizeTy -> TyFun _ a b)) = Just (Just a, Just b)
    funTypeView _ = Nothing

    -- Generate builtin ifthenelse and trace calls
    genIfTrace = do
      fun <- liftGen $ elements [IfThenElse, Trace]
      pure (typeOfBuiltinFunction def fun, Builtin () fun)

    genError Nothing = do
      ty <- genType $ Type ()
      return (ty, Error () ty)
    genError (Just ty) = return (ty, Error () ty)

    canConst Nothing = True
    canConst (Just TyBuiltin {}) = True
    canConst (Just _) = False

    genConst Nothing = do
      someUni <- deliver . liftGen . genBuiltinTypeOf $ Type ()
      (TyBuiltin () someUni,) <$> genConstant someUni
    genConst (Just ty@(TyBuiltin _ someUni)) = (ty,) <$> genConstant someUni
    genConst _ = error "genConst: impossible"

    genDatLet mty = do
      rec <- liftGen arbitrary
      genDatatypeLet rec $ \dat -> do
        (ty, tm) <- genTerm mty
        return $ (ty, Let () (if rec then Rec else NonRec) (DatatypeBind () dat :| []) tm)

    genLet mty = do
      -- How many terms to bind
      n <- liftGen $ choose (1, 3)
      -- Names of the bound terms
      xs <- genLikelyFreshNames $ replicate n "f"
      -- Types of the bound terms
      -- TODO: generate something that matches the target type
      as <- onAstSize (`div` 8) $ vectorOf n $ genType (Type ())
      -- Strictness
      ss <- vectorOf n $ liftGen $ elements [Strict, NonStrict]
      -- Recursive?
      r <- liftGen $ frequency [(1, pure True), (6, pure False)]
      -- Generate the binding
      -- TODO: maybe also generate mutually recursive bindings?
      let genBin (x, a)
            | r = withNoEscape . bindTmName x a . genTermOfType $ a
            | otherwise = withNoEscape . genTermOfType $ a
      -- Generate both bound terms and body with a size split of 1:7 (note, we are generating up to three bound
      -- terms, so the size split is really something like n:7).
      (tms, (ty, body)) <-
        astSizeSplit_ 1 7 (mapM genBin (zip xs as)) (bindTmNames (zip xs as) $ genTerm mty)
      let mkBind (x, a, s) tm =
            TermBind
              ()
              s
              (VarDecl () x a)
              tm
          b : bs = zipWith mkBind (zip3 xs as ss) tms
      pure (ty, Let () (if r then Rec else NonRec) (b :| bs) body)

    genForall x k a = do
      -- TODO: this freshenTyName here might be a bit paranoid
      y <- freshenTyNameWith (setOf ftvTy a) <$> genLikelyFreshTyName "a"
      let ty = TyForall () y k $ renameVar x y a
      (ty,) . TyAbs () y k <$> (withNoEscape . bindTyName y k . genTermOfType $ renameVar x y a)

    genLam ma mb = do
      x <- genLikelyFreshName "x"
      (a, (b, body)) <-
        astSizeSplit
          1
          7
          (maybe (genType $ Type ()) return ma)
          (\a -> bindTmName x a . withNoEscape $ genTerm mb)
      pure (TyFun () a b, LamAbs () x a body)

    genApp mty = withNoEscape $ do
      ((_, arg), (toResTy, fun)) <-
        astSizeSplit 1 4 (genTerm Nothing) (\(argTy, _) -> genFun argTy mty)
      case toResTy of
        TyFun _ _ resTy -> pure (resTy, Apply () fun arg)
        _ -> error $ display toResTy ++ "\n\n is not a 'TyFun'"
      where
        genFun argTy mty = genTerm . Just . TyFun () argTy =<< maybe (genType (Type ())) pure mty

    genVarApp :: HasCallStack => _
    genVarApp Nothing = withNoEscape $ do
      -- CODE REVIEW: this function exists somewhere maybe? (Maybe even in this module...)
      let arity (TyForall _ _ _ b) = 1 + arity b
          arity (TyFun _ _ b) = 1 + arity b
          arity _ = 0

          appl :: HasCallStack => Int -> Term TyName Name DefaultUni DefaultFun () -> _
          appl 0 tm b = return (b, tm)
          appl n tm (TyForall _ x k b) = do
            ty <- genType k
            x' <- genLikelyFreshTyName "x"
            appl (n - 1) (TyInst () tm ty) (substType (Map.singleton x' ty) $ renameVar x x' b)
          appl n tm (TyFun _ a b) = do
            (_, arg) <- genTerm (Just a)
            appl (n - 1) (Apply () tm arg) b
          appl _ _ _ = error "appl"

          genV (x, ty0) = do
            let ty = normalizeTy ty0
            n <- liftGen $ choose (0, arity ty)
            onAstSize (`div` n) $ appl n (Var () x) ty
      asks (Map.toList . geTerms) >>= \case
        [] -> do
          ty <- genType $ Type ()
          (ty,) <$> inhabitType ty
        vars -> oneof $ map genV vars
    genVarApp (Just ty) = do
      vars <- asks geTerms
      ctx <- asks geTypes
      let cands = Map.toList vars
          doInst _ tm (InstApp instTy) = pure $ TyInst () tm instTy
          doInst n tm (InstArg argTy) =
            onAstSize ((`div` n) . subtract 1)
              . withNoEscape
              $ Apply () tm <$> genTermOfType argTy
      case [ foldM (doInst n) (Var () x) insts
           | (x, a) <- cands
           , n <- [0 .. typeArity a]
           , Right insts <- [findInstantiation ctx n ty a]
           ] of
        [] -> (ty,) <$> inhabitType ty
        gs -> (ty,) <$> oneof gs

-- | Like 'listOf' except each of the elements is generated with a proportionally smaller size.
scaledListOf :: GenTm a -> GenTm [a]
scaledListOf g = do
  sz <- asks geAstSize
  n <- choose (0, sz `div` 3)
  onAstSize (`div` n) $ replicateM n g

genDatatypeLet :: Bool -> (Datatype TyName Name DefaultUni () -> GenTm a) -> GenTm a
genDatatypeLet rec cont = do
  k0 <- liftGen arbitrary
  let ks = argsFunKind k0
  n <- liftGen $ choose (1, 3)
  -- Lazy matching to communicate to GHC the fact that this can't fail and thus doesn't require
  -- a 'MonadFail' (which 'GenTm' isn't).
  ~(d : xs) <- genLikelyFreshTyNames $ "d" : replicate (length ks) "a"
  ~(m : cs) <- genLikelyFreshNames $ "m" : replicate n "c"
  let dTy = foldl (TyApp ()) (TyVar () d) [TyVar () x | x <- xs]
      bty d =
        if rec
          then bindTyName d k0
          else registerTyName d
  conArgss <-
    bty d $
      bindTyNames (zip xs ks) $
        -- Using 'listOf' instead if 'scaledListOf' makes the code slower by several
        -- times (didn't check how exactly it affects the generated types).
        onAstSize (`div` n) $
          replicateM n $
            scaledListOf (genType $ Type ())
  let dat =
        Datatype
          ()
          (TyVarDecl () d k0)
          [TyVarDecl () x k | (x, k) <- zip xs ks]
          m
          [ VarDecl () c (foldr (TyFun ()) dTy conArgs)
          | (c, conArgs) <- zip cs conArgss
          ]
  bindDat dat $ cont dat

{-| Generate up to 5 datatypes and bind them in a generator.
NOTE: despite its name this function does in fact not generate the `Let` binding
for the datatypes. -}
genDatatypeLets :: ([Datatype TyName Name DefaultUni ()] -> GenTm a) -> GenTm a
genDatatypeLets cont = do
  n0 <- liftGen $ choose (1, 5 :: Int)
  let go 0 k = k []
      go n k = genDatatypeLet False $ \dat -> go (n - 1) (k . (dat :))
  go n0 cont

genTypeAndTerm_ :: Gen (Type TyName DefaultUni (), Term TyName Name DefaultUni DefaultFun ())
genTypeAndTerm_ = runGenTm $ do
  (ty, body) <- genTerm Nothing
  return (ty, body)

genTypeAndTermDebug_ :: Gen (Type TyName DefaultUni (), Term TyName Name DefaultUni DefaultFun ())
genTypeAndTermDebug_ = runGenTm . withDebug $ do
  (ty, body) <- genTerm Nothing
  return (ty, body)

{-| Take a term of a specified type and generate
a fully applied term. Useful for generating terms that you want
to stick directly in an interpreter. Prefers to generate small arguments.
NOTE: The logic of this generating small arguments is that the inner term
should already have plenty of complicated arguments to functions to begin
with and now we just want to fill out the arguments so that we get
something that hopefully evaluates for a non-trivial number of steps. -}
genFullyApplied
  :: Type TyName DefaultUni ()
  -> Term TyName Name DefaultUni DefaultFun ()
  -> Gen (Type TyName DefaultUni (), Term TyName Name DefaultUni DefaultFun ())
genFullyApplied typ0 trm0 = runGenTm $ go trm0
  where
    go trm = case trm of
      Let () rec binds body -> second (Let () rec binds) <$> bindBinds binds (go body)
      _ -> genArgsApps typ0 trm
    genArgsApps (TyForall _ x k typ) trm = do
      let ty = minimalType k
      genArgsApps (typeSubstClosedType x ty typ) (TyInst () trm ty)
    genArgsApps (TyFun _ a b) trm = do
      (_, arg) <- withNoEscape $ genTerm (Just a)
      genArgsApps b (Apply () trm arg)
    genArgsApps ty trm = return (ty, trm)

-- | Generate a term of a specific type given a type and term context
genTermInContext_
  :: TypeCtx
  -> Map Name (Type TyName DefaultUni ())
  -> Type TyName DefaultUni ()
  -> Gen (Term TyName Name DefaultUni DefaultFun ())
genTermInContext_ tyctx ctx ty =
  runGenTm $
    local (\e -> e {geTypes = tyctx, geTerms = ctx, geEscaping = NoEscape}) $
      snd <$> genTerm (Just ty)
