-- editorconfig-checker-disable-file
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE TupleSections         #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE UndecidableInstances  #-}
{-# LANGUAGE ViewPatterns          #-}

{-# OPTIONS_GHC -Wno-name-shadowing #-}
{-# OPTIONS_GHC -Wno-incomplete-uni-patterns #-}
{-# OPTIONS_GHC -Wno-partial-type-signatures #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module PlutusIR.Generators.QuickCheck.GenerateTerms where

import PlutusCore.Generators.QuickCheck.Builtin
import PlutusCore.Generators.QuickCheck.Common
import PlutusCore.Generators.QuickCheck.GenerateTypes
import PlutusCore.Generators.QuickCheck.GenTm
import PlutusCore.Generators.QuickCheck.ShrinkTypes
import PlutusCore.Generators.QuickCheck.Substitutions
import PlutusCore.Generators.QuickCheck.Unification
import PlutusCore.Generators.QuickCheck.Utils

import PlutusCore.Builtin
import PlutusCore.Core (argsFunKind)
import PlutusCore.Data
import PlutusCore.Default
import PlutusCore.MkPlc (mkConstant, mkConstantOf, mkTyBuiltin)
import PlutusCore.Name
import PlutusCore.Quote (runQuoteT)
import PlutusCore.Rename
import PlutusCore.Subst (typeSubstClosedType)
import PlutusIR
import PlutusIR.Compiler
import PlutusIR.Core.Instance.Pretty.Readable
import PlutusIR.Error
import PlutusIR.Subst
import PlutusIR.TypeCheck

import Control.Applicative ((<|>))
import Control.Lens ((<&>))
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
import Test.QuickCheck (shrinkList)
import Text.PrettyBy

-- CODE REVIEW: where to put the stuff below? Can we refactor to the point where we don't need them?
-- Currently we need these for shrinking, getting rid of them would be nice.
deriving stock instance Eq (Term TyName Name DefaultUni DefaultFun ())
deriving stock instance Eq (Binding TyName Name DefaultUni DefaultFun ())
deriving stock instance Eq (VarDecl TyName Name DefaultUni ())
deriving stock instance Eq (TyVarDecl TyName ())
deriving stock instance Eq (Datatype TyName Name DefaultUni ())

addTmBind :: Binding TyName Name DefaultUni DefaultFun ()
          -> Map Name (Type TyName DefaultUni ())
          -> Map Name (Type TyName DefaultUni ())
addTmBind (TermBind _ _ (VarDecl _ x a) _) = Map.insert x a
addTmBind (DatatypeBind _ dat)             = (Map.fromList (matchType dat : constrTypes dat) <>)
addTmBind _                                = id

-- | This type keeps track of what kind of argument, term argument (`InstArg`) or
-- type argument (`InstApp`) is required for a function. This type is used primarily
-- with `findInstantiation` below where we do unification to figure out if we can
-- use a variable to construct a term of a target type.
data TyInst = InstApp (Type TyName DefaultUni ()) | InstArg (Type TyName DefaultUni ())
  deriving stock Show

instance PrettyBy config (Type TyName DefaultUni ()) => PrettyBy config TyInst where
  prettyBy ctx (InstApp ty) = prettyBy ctx ty
  prettyBy ctx (InstArg ty) = brackets (prettyBy ctx ty)

-- | If successful `findInstantiation n target ty` for an `x :: ty` gives a sequence of `TyInst`s containing `n`
--   `InstArg`s such that `x` instantiated (type application for `InstApp` and applied to a term of
--   the given type for `InstArg`) at the `TyInsts`s has type `target`
findInstantiation :: HasCallStack
                  => TypeCtx
                  -> Int
                  -> Type TyName DefaultUni ()
                  -> Type TyName DefaultUni ()
                  -> Either String [TyInst]
findInstantiation ctx n target ty = do
  sub <- unifyType (ctx <> ctx') flex target b
      -- We map any unsolved flexible variables to ∀ a. a
  let defaultSub = minimalType <$> ctx'
      doSub :: HasCallStack => _
      doSub = substType defaultSub . substType sub
      doSubI (InstApp t) = InstApp (doSub t)
      doSubI (InstArg t) = InstArg (doSub t)
  pure $ map doSubI insts
  where
    fvs = setOf ftvTy target <> setOf ftvTy ty <> Map.keysSet ctx
    (ctx', flex, insts, b) = view Map.empty Set.empty [] n fvs ty

    -- TODO: documentation!
    view ctx' flex insts n fvs (TyForall _ x k b) = view (Map.insert x' k ctx') (Set.insert x' flex)
                                                         (InstApp (TyVar () x') : insts) n
                                                         (Set.insert x' fvs) b'
      where (x', b') | Set.member x fvs = let x' = freshenTyNameWith fvs x in (x', renameVar x x' b)
                     | otherwise        = (x, b)
    view ctx' flex insts n fvs (TyFun _ a b) | n > 0 = view ctx' flex (InstArg a : insts) (n - 1) fvs b
    view ctx' flex insts _ _ a = (ctx', flex, reverse insts, a)

genConstant :: SomeTypeIn DefaultUni -> GenTm (Term TyName Name DefaultUni DefaultFun ())
genConstant (SomeTypeIn b) = case toSingKind b of
    SingType -> mkConstantOf () b <$> bring (Proxy @ArbitraryBuiltin) b (liftGen arbitraryBuiltin)
    _        -> error "Higher-kinded built-in types cannot be used here"

shrinkConstant :: DefaultUni (Esc a) -> a -> [Term TyName Name DefaultUni DefaultFun ()]
shrinkConstant uni x =
    map (mkConstantOf () uni) $ bring (Proxy @ArbitraryBuiltin) uni $ shrinkBuiltin x

-- | Try to inhabit a given type in as simple a way as possible,
-- prefers to not default to `error`
inhabitType :: Type TyName DefaultUni () -> GenTm (Term TyName Name DefaultUni DefaultFun ())
inhabitType ty = local (\ e -> e { geTerms = mempty }) $ do
  either error id <$> runExceptT (findTm ty <|> pure (Error () ty))
  where
    -- Do the obvious thing as long as target type is not type var
    -- When type var: magic (if higher-kinded type var: black magic)
    -- Ex: get `a` from D ts ==> get `a` from which ts, get which params from D
    -- This function does not fail to error.
    --
    -- NOTE: because we make recursive calls to findTm in this function instead of
    -- inhabitType we don't risk generating terms that are "mostly ok but something is error",
    -- this function will avoid error if possible.
    findTm :: Type TyName DefaultUni ()
           -> ExceptT String GenTm (Term TyName Name DefaultUni DefaultFun ())
    findTm (normalizeTy -> ty) = case ty of
      TyFun _ a b -> do
        x <- lift $ genLikelyFreshName "x"
        LamAbs () x a <$> mapExceptT (bindTmName x a) (findTm b)
      TyForall _ x k b -> do
        TyAbs () x k <$> mapExceptT (bindTyName x k) (findTm b)
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
                    -- type application with type required by findInstantiation
                    doInst _ tm (InstApp instTy) = pure $ TyInst () tm instTy
                    -- If we instantiate an application, only succeed if we find
                    -- a non-error argument.
                    doInst _ tm (InstArg argTy)  = Apply () tm <$> findTm argTy
                -- Go over every type and try to inhabit the type at the arguments
                case [ local (\e -> e { geTerms = Map.delete x' (geTerms e) })
                       $ foldM (doInst n) (Var () x') insts
                     | (x', a)     <- cands,
                       n           <- [0..typeArity a],
                       Right insts <- [findInstantiation ctx n ty a],
                       x `Set.notMember` fvArgs a
                     ] of
                  [] -> mzero
                  gs -> head gs
          _ -> mzero

    -- Try to inhabit a constructor `con` of type `conTy` in datatype `d` at type `ty`
    tryCon d ty (con, conTy)
      | Set.member d (fvArgs conTy) = mzero   -- <- This is ok, since no mutual recursion
      | otherwise = do
          -- Check that we haven't banned this constructor
          tmctx <- lift $ asks geTerms
          if Map.lookup con tmctx == Just conTy
          then do
            tyctx <- lift $ asks geTypes
            insts <- liftEither $ findInstantiation tyctx (typeArity conTy) ty conTy
            let go tm [] = return tm
                go tm (InstApp ty : insts) = go (TyInst () tm ty) insts
                go tm (InstArg ty : insts) = do
                  arg <- findTm ty
                  go (Apply () tm arg) insts
            go (Var () con) insts
          else mzero

    -- CODE REVIEW: wouldn't it be neat if this existed somewhere?
    viewApp args (TyApp _ f x) = viewApp (x : args) f
    viewApp args ty            = (ty, args)

    -- Get the free variables that appear in arguments of a mixed arrow-forall type
    fvArgs (TyForall _ x _ b) = Set.delete x (fvArgs b)
    fvArgs (TyFun _ a b)      = setOf ftvTy a <> fvArgs b
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
  let unifyVar (x, xty) = findInstantiation ctx 0 ty xty
                       <&> \ tys -> foldl (TyInst ()) (Var () x) [t | InstApp t <- tys]
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

-- | Generate a term of a given type.
--
-- Requires the type to be of kind *.
genTermOfType :: Type TyName DefaultUni ()
              -> GenTm (Term TyName Name DefaultUni DefaultFun ())
genTermOfType ty = snd <$> genTerm (Just ty)

-- | Generate a term, if the first argument is Nothing then we get something of any type
-- and if the first argument is `Just ty` we get something of type `ty`.
--
-- Requires the type to be of kind *.
genTerm :: Maybe (Type TyName DefaultUni ())
        -> GenTm (Type TyName DefaultUni (), Term TyName Name DefaultUni DefaultFun ())
genTerm mty = checkInvariants $ do
  customF <- asks geCustomFreq
  customG <- asks geCustomGen
  vars <- asks geTerms
  esc <- asks geEscaping
  -- Prefer to generate things that bind variables until we have "enough" (20...)
  let (letF, lamF, varAppF) = if Map.size vars < 20
                              then (30, 50, 10)
                              else (10, 30, 40)
      atomic
          | Just ty <- mty = (ty,) <$> genAtomicTerm ty
          | otherwise      = do
              ty <- genType $ Type ()
              (ty,) <$> genAtomicTerm ty
  ifAstSizeZero atomic $
    frequency $
      [ (10, atomic) ]                                             ++
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

    checkInvariants gen = do
      (ty, tm) <- gen
      debug    <- asks geDebug
      tyctx    <- asks geTypes
      tmctx    <- asks geTerms
      if debug then
        case typeCheckTermInContext tyctx tmctx tm ty of
          Left err ->
             (error . show $ "genTerm - checkInvariants: term " <> prettyPirReadable tm
                           <> " does not type check at type " <> prettyPirReadable ty
                           <> " in type context " <> prettyPirReadable tyctx
                           <> " and term context " <> prettyPirReadable tmctx
                           <> " with error message " <> fromString err)
          _ -> return (ty, tm)
      else
        return (ty, tm)

    funTypeView Nothing                             = Just (Nothing, Nothing)
    funTypeView (Just (normalizeTy -> TyFun _ a b)) = Just (Just a, Just b)
    funTypeView _                                   = Nothing

    -- Generate builtin ifthenelse and trace calls
    genIfTrace = do
      fun <- liftGen $ elements [IfThenElse, Trace]
      pure (typeOfBuiltinFunction def fun, Builtin () fun)

    genError Nothing = do
      ty <- genType $ Type ()
      return (ty, Error () ty)
    genError (Just ty) = return (ty, Error () ty)

    canConst Nothing            = True
    canConst (Just TyBuiltin{}) = True
    canConst (Just _)           = False

    genConst Nothing = do
      b <- deliver . liftGen . genBuiltinTypeOf $ Type ()
      (TyBuiltin () b, ) <$> genConstant b
    genConst (Just ty@(TyBuiltin _ b)) = (ty,) <$> genConstant b
    genConst _ = error "genConst: impossible"

    genDatLet mty = do
      rec <- liftGen arbitrary
      genDatatypeLet rec $ \ dat -> do
        (ty, tm) <- genTerm mty
        return $ (ty, Let () (if rec then Rec else NonRec) (DatatypeBind () dat :| []) tm)

    genLet mty = do
      -- How many terms to bind
      n   <- liftGen $ choose (1, 3)
      -- Names of the bound terms
      xs  <- genLikelyFreshNames $ replicate n "f"
      -- Types of the bound terms
      -- TODO: generate something that matches the target type
      as  <- onAstSize (`div` 8) $ vectorOf n $ genType (Type ())
      -- Strictness
      ss  <- vectorOf n $ liftGen $ elements [Strict, NonStrict]
      -- Recursive?
      r   <- liftGen $ frequency [(5, pure True), (30, pure False)]
      -- Generate the binding
      -- TODO: maybe also generate mutually recursive bindings?
      let genBin (x, a) | r         = withNoEscape . bindTmName x a . genTermOfType $ a
                        | otherwise = withNoEscape . genTermOfType $ a
      -- Generate both bound terms and body with a size split of 1:7 (note, we are generating up to three bound
      -- terms, so the size split is really something like n:7).
      (tms, (ty, body)) <-
          astSizeSplit_ 1 7 (mapM genBin (zip xs as)) (bindTmNames (zip xs as) $ genTerm mty)
      let mkBind (x, a, s) tm = TermBind () s
                                  (VarDecl () x a) tm
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
        astSizeSplit 1 7
          (maybe (genType $ Type ()) return ma)
          (\ a -> bindTmName x a . withNoEscape $ genTerm mb)
      pure (TyFun () a b, LamAbs () x a body)

    genApp mty = withNoEscape $ do
        ((_, arg), (toResTy, fun)) <-
          astSizeSplit 1 4 (genTerm Nothing) (\ (argTy, _) -> genFun argTy mty)
        case toResTy of
          TyFun _ _ resTy -> pure (resTy, Apply () fun arg)
          _               -> error $ display toResTy ++ "\n\n is not a 'TyFun'"
      where
        genFun argTy mty = genTerm . Just . TyFun () argTy =<< maybe (genType (Type ())) pure mty

    genVarApp :: HasCallStack => _
    genVarApp Nothing = withNoEscape $ do
      -- CODE REVIEW: this function exists somewhere maybe? (Maybe even in this module...)
      let arity (TyForall _ _ _ b) = 1 + arity b
          arity (TyFun _ _ b)      = 1 + arity b
          arity _                  = 0

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
      asks (Map.toList . geTerms) >>= \ case
        []   -> do
          ty <- genType $ Type ()
          (ty,) <$> inhabitType ty
        vars -> oneof $ map genV vars

    genVarApp (Just ty) = do
      vars <- asks geTerms
      ctx  <- asks geTypes
      let cands = Map.toList vars
          doInst _ tm (InstApp instTy) = pure $ TyInst () tm instTy
          doInst n tm (InstArg argTy)  = onAstSize ((`div` n) . subtract 1)
                                       . withNoEscape
                                       $ Apply () tm <$> genTermOfType argTy
      case [ foldM (doInst n) (Var () x) insts
           | (x, a)      <- cands,
             n           <- [0..typeArity a],
             Right insts <- [findInstantiation ctx n ty a]
           ] of
        [] -> (ty,) <$> inhabitType ty
        gs -> (ty,) <$> oneof gs

-- | Like 'liftOf' except each of the elements is generated with a proportionally smaller size.
scaledListOf :: GenTm a -> GenTm [a]
scaledListOf g = do
  sz <- asks geAstSize
  n  <- choose (0, sz `div` 3)
  onAstSize (`div` n) $ replicateM n g

genDatatypeLet :: Bool -> (Datatype TyName Name DefaultUni () -> GenTm a) -> GenTm a
genDatatypeLet rec cont = do
    k <- liftGen arbitrary
    let ks = argsFunKind k
    n <- liftGen $ choose (1, 3)
    ~(d : xs) <- genLikelyFreshTyNames $ "d" : replicate (length ks) "a"
    ~(m : cs) <- genLikelyFreshNames   $ "m" : replicate n "c"
    let dTy = foldl (TyApp ()) (TyVar () d) [TyVar () x | x <- xs]
        bty d = if rec
                then bindTyName d k
                else registerTyName d
    conArgss <- bty d $ bindTyNames (zip xs ks) $
                  -- Using 'listOf' instead if 'scaledListOf' makes the code slower by several
                  -- times (didn't check how exactly it affects the generated types).
                  onAstSize (`div` n) $ replicateM n $ scaledListOf (genType $ Type ())
    let dat = Datatype () (TyVarDecl () d k) [TyVarDecl () x k | (x, k) <- zip xs ks] m
                       [ VarDecl () c (foldr (TyFun ()) dTy conArgs)
                       | (c, conArgs) <- zip cs conArgss ]
                       -- TODO: it might make sense to do a negativity test here -
                       -- but not clear how important that is.
    bindDat dat $ cont dat

-- | Generate up to 5 datatypes and bind them in a generator.
-- NOTE: despite its name this function does in fact not generate the `Let` binding
-- for the datatypes.
genDatatypeLets :: ([Datatype TyName Name DefaultUni ()] -> GenTm a) -> GenTm a
genDatatypeLets cont = do
  n <- liftGen $ choose (1, 5 :: Int)
  let go 0 k = k []
      go n k = genDatatypeLet False $ \ dat -> go (n - 1) (k . (dat :))
  go n cont

shrinkClosedTypedTerm :: (Type TyName DefaultUni (), Term TyName Name DefaultUni DefaultFun ())
                      -> [(Type TyName DefaultUni (), Term TyName Name DefaultUni DefaultFun ())]
shrinkClosedTypedTerm = shrinkTypedTerm mempty mempty

scopeCheckTyVars :: TypeCtx
                 -> (Type TyName DefaultUni (), Term TyName Name DefaultUni DefaultFun ())
                 -> Bool
scopeCheckTyVars tyctx (ty, tm) = all (`Set.member` inscope) (setOf ftvTy ty)
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
-- idea to look at how we do this for types first (it's a lot simpler).
shrinkTypedTerm :: HasCallStack
                => TypeCtx
                -> Map Name (Type TyName DefaultUni ())
                -> (Type TyName DefaultUni (), Term TyName Name DefaultUni DefaultFun ())
                -> [(Type TyName DefaultUni (), Term TyName Name DefaultUni DefaultFun ())]
shrinkTypedTerm tyctx ctx (ty, tm) = go tyctx ctx (ty, tm)
  where
    isHelp _ (Constant _ _)           = True
    isHelp ctx (TyInst _ (Var _ x) _) = Just x == findHelp ctx
    isHelp _ (Error _ _)              = True
    isHelp _ _                        = False

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
      [ (ty', tm') | not $ isHelp ctx tm
                   , ty' <- ty : shrinkType (tyctx <> Map.fromList (datatypes tm)) ty
                   , let tm' = mkHelp ctx ty' ] ++
      case tm of

        -- TODO: shrink Rec to NonRec
        Let _ rec binds body ->
          [ case binds of
              []   -> (letTy, letTm)
              b:bs -> (letTy, Let () NonRec (b :| bs) letTm)
          | (NonEmptyContext binds _, TermBind _ _ (VarDecl _ _ letTy) letTm) <- oneHoleContexts binds
          , rec == NonRec
          ] ++
          [ second (Let () rec (b :| binds'))
            $ fixupTerm_ tyctxInner ctxInner tyctxInner' ctxInner' ty body
          | (NonEmptyContext binds0 binds1, _) <- oneHoleContexts binds,
            let tyctxInner  = foldr addTyBind tyctx binds
                ctxInner    = foldr addTmBind ctx   binds
                tyctxInner' = foldr addTyBind tyctx (binds0 ++ binds1)
                ctxInner'   = foldr addTmBind ctx   (binds0 ++ binds1)
          , b:binds' <- [binds0 ++ binds1]
          ] ++
          [ fixupTerm_ tyctxInner ctxInner tyctx ctx ty body
          | let tyctxInner  = foldr addTyBind tyctx binds
                ctxInner    = foldr addTmBind ctx   binds ]

        LamAbs _ x a body ->
          [ fixupTerm_ tyctx (Map.insert x a ctx) tyctx ctx b body
          | TyFun _ _ b <- [ty] ] ++
          [ (b, body)
          | TyFun _ _ b <- [ty]
          , x `Set.notMember` setOf fvTerm body ]

        Apply _ fun arg | Right argTy <- inferTypeInContext tyctx ctx arg ->
          -- Drop substerms
          [(argTy, arg), (TyFun () argTy ty, fun)] ++
          -- Shrink subterms (TODO: this is really two-step shrinking and might not be necessary)
          go tyctx ctx (TyFun () argTy ty, fun) ++
          go tyctx ctx (argTy, arg)

        TyAbs _ x _ body ->
          [ fixupTerm_ (Map.insert x k tyctx) ctx tyctx ctx tyInner' body
          | TyForall _ y k tyInner <- [ty]
          , let tyInner' = typeSubstClosedType y (minimalType k) tyInner
          ]

        -- Builtins can shrink to unit. More fine-grained shrinking is in `structural` below.
        Constant _ (Some (ValueOf uni _)) -> case uni of
            DefaultUniUnit -> []
            _              -> [(mkTyBuiltin @_ @() (), mkConstant () ())]

        _ -> []

    -- These are the structural (basically homomorphic) cases in shrinking.
    -- They all just try to shrink a single subterm at a time. We also
    -- use fixupTerm to adjust types here in a trick similar to how we shrunk
    -- types above.
    structural :: HasCallStack => _
    structural tyctx ctx (ty, tm) =
      case tm of

        Let _ rec binds body ->
          [ (substTypeParallel subst ty', Let () rec binds body')
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
                  fix = uncurry (fixupTerm_ tyctx ctx tyctx ctx)
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
          , (tyInner', body') <- go (Map.insert x k tyctx) ctx (renameVar y x tyInner, body)
          ]

        LamAbs _ x a body ->
          [ (TyFun () a b', LamAbs () x a body')
          | TyFun _ _ b <- [ty],
            (b', body') <- go tyctx (Map.insert x a ctx) (b, body)
          ] ++
          [ bimap (TyFun () a') (LamAbs () x a') $
              fixupTerm_ tyctx (Map.insert x a ctx) tyctx (Map.insert x a' ctx) b body
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

        Constant _ (Some (ValueOf uni x)) -> map ((,) ty) $ shrinkConstant uni x

        _ -> []

-- | Try to infer the type of an expression in a given type and term context.
-- NOTE: one can't just use out-of-the-box type inference here because the
-- `inferType` algorithm happy renames things.
inferTypeInContext :: TypeCtx
                   -> Map Name (Type TyName DefaultUni ())
                   -> Term TyName Name DefaultUni DefaultFun ()
                   -> Either String (Type TyName DefaultUni ())
inferTypeInContext tyctx ctx tm = first display
                                $ runQuoteT @(Either (Error DefaultUni DefaultFun ())) $ do
  -- CODE REVIEW: this algorithm is fragile, it relies on knowing that `inferType`
  -- does renaming to compute the `esc` substitution for datatypes. However, there is also
  -- not any other way to do this in a way that makes type inference actually useful - you
  -- want to do type inference in non-top-level contexts. Ideally I think type inference
  -- probably shouldn't do renaming of datatypes... Or alternatively we need to ensure that
  -- the renaming behaviour of type inference is documented and maintained.
  cfg <- getDefTypeCheckConfig ()
  -- Infer the type of `tm` by adding the contexts as (type and term) lambdas
  Normalized _ty' <- inferType cfg tm'
  -- Substitute the free variables and escaping datatypes to get back to the un-renamed type.
  let ty' = substEscape (Map.keysSet esc <> foldr (<>) (setOf ftvTy _ty') (setOf ftvTy <$> esc)) esc _ty' -- yuck
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

    stripForalls sub [] ty                            = substTypeParallel sub ty
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

-- | Try to find a variable of type `forall x. x` in the context.
findHelp :: Map Name (Type TyName DefaultUni ()) -> Maybe Name
findHelp ctx =
  case Map.toList $ Map.filter isHelpType ctx of
    []         -> Nothing
    (x, _) : _ -> Just x
  where
    isHelpType (TyForall _ x (Type ()) (TyVar _ x')) = x == x'
    isHelpType _                                     = False

-- | Try to take a term from an old context to a new context and a new type.
-- If we can't do the new type we might return a different type.
fixupTerm_ :: TypeCtx
           -> Map Name (Type TyName DefaultUni ())
           -> TypeCtx
           -> Map Name (Type TyName DefaultUni ())
           -> Type TyName DefaultUni ()
           -> Term TyName Name DefaultUni DefaultFun ()
           -> (Type TyName DefaultUni (), Term TyName Name DefaultUni DefaultFun ())
fixupTerm_ tyctxOld ctxOld tyctxNew ctxNew tyNew tm =
  case inferTypeInContext tyctxNew ctxNew tm of
    Left _ -> case tm of
      LamAbs _ x a tm | TyFun () _ b <- tyNew -> bimap (TyFun () a) (LamAbs () x a)
                                              $ fixupTerm_ tyctxOld (Map.insert x a ctxOld)
                                                           tyctxNew (Map.insert x a ctxNew) b tm
      Apply _ (Apply _ (TyInst _ (Builtin _ Trace) _) s) tm ->
        let (ty', tm') = fixupTerm_ tyctxOld ctxOld tyctxNew ctxNew tyNew tm
        in (ty', Apply () (Apply () (TyInst () (Builtin () Trace) ty') s) tm')
      _ | TyBuiltin _ b <- tyNew -> (tyNew, minimalBuiltin b)
        | otherwise -> (tyNew, mkHelp ctxNew tyNew)
    Right ty -> (ty, tm)

-- | Try to take a term from an old context to a new context and a new type - default to `mkHelp`.
fixupTerm :: TypeCtx
          -> Map Name (Type TyName DefaultUni ())
          -> TypeCtx
          -> Map Name (Type TyName DefaultUni ())
          -> Type TyName DefaultUni ()
          -> Term TyName Name DefaultUni DefaultFun ()
          -> Term TyName Name DefaultUni DefaultFun ()
fixupTerm _ _ tyctxNew ctxNew tyNew tm
  | isRight (typeCheckTermInContext tyctxNew ctxNew tm tyNew) = tm
  | otherwise                                                 = mkHelp ctxNew tyNew

minimalBuiltin :: SomeTypeIn DefaultUni -> Term TyName Name DefaultUni DefaultFun ()
minimalBuiltin (SomeTypeIn b) = case toSingKind b of
    SingType -> mkConstantOf () b $ go b
    _        -> error "Higher-kinded built-in types cannot be used here"
  where
    go :: DefaultUni (Esc a) -> a
    go DefaultUniUnit                                                   = ()
    go DefaultUniInteger                                                = 0
    go DefaultUniBool                                                   = False
    go DefaultUniString                                                 = ""
    go DefaultUniByteString                                             = ""
    go DefaultUniData                                                   = I 0
    go (DefaultUniProtoList `DefaultUniApply` _)                        = []
    go (DefaultUniProtoPair `DefaultUniApply` a `DefaultUniApply` b)    = (go a, go b)
    go (f  `DefaultUniApply` _ `DefaultUniApply` _ `DefaultUniApply` _) = noMoreTypeFunctions f

shrinkBind :: HasCallStack
           => Recursivity
           -> TypeCtx
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

shrinkDat :: TypeCtx
          -> Datatype TyName Name DefaultUni ()
          -> [Datatype TyName Name DefaultUni ()]
shrinkDat ctx (Datatype _ dd@(TyVarDecl _ d _) xs m cs) =
  [ Datatype () dd xs m cs' | cs' <- shrinkList shrinkCon cs ]
  where
    ctx' = ctx <> Map.fromList [ (x, k) | TyVarDecl _ x k <- xs ]
    shrinkCon (VarDecl _ c ty) = [ VarDecl () c ty''
                                 | ty' <- shrinkType ctx' ty
                                 , let ty'' = setTarget (getTarget ty) ty'
                                 , ty'' /= ty
                                 , d `Set.notMember` setOf ftvTy (setTarget (mkTyBuiltin @_ @() ()) ty') ]
      where
        getTarget (TyFun _ _ b) = getTarget b
        getTarget b             = b
        setTarget t (TyFun _ a b) = TyFun () a (setTarget t b)
        setTarget t _             = t

genTypeAndTerm_ :: Gen (Type TyName DefaultUni (), Term TyName Name DefaultUni DefaultFun ())
genTypeAndTerm_ = runGenTm $ do
  (ty, body) <- genTerm Nothing
  return (ty, body)

genTypeAndTermDebug_ :: Gen (Type TyName DefaultUni (), Term TyName Name DefaultUni DefaultFun ())
genTypeAndTermDebug_ = runGenTm . withDebug $ do
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
      genArgsApps (typeSubstClosedType x ty typ) (TyInst () trm ty)
    genArgsApps (TyFun _ a b) trm = do
      (_, arg) <- withNoEscape $ genTerm (Just a)
      genArgsApps b (Apply () trm arg)
    genArgsApps ty trm = return (ty, trm)

-- | Generate a term of a specific type given a type and term context
genTermInContext_ :: TypeCtx
                  -> Map Name (Type TyName DefaultUni ())
                  -> Type TyName DefaultUni ()
                  -> Gen (Term TyName Name DefaultUni DefaultFun ())
genTermInContext_ tyctx ctx ty =
  runGenTm $ local (\ e -> e { geTypes = tyctx, geTerms = ctx, geEscaping = NoEscape }) $
    snd <$> genTerm (Just ty)

typeCheckTerm :: Term TyName Name DefaultUni DefaultFun ()
              -> Type TyName DefaultUni ()
              -> Either String ()
typeCheckTerm = typeCheckTermInContext Map.empty Map.empty

typeCheckTermInContext :: TypeCtx
                       -> Map Name (Type TyName DefaultUni ())
                       -> Term TyName Name DefaultUni DefaultFun ()
                       -> Type TyName DefaultUni ()
                       -> Either String ()
typeCheckTermInContext tyctx ctx tm ty = void $ do
    ty' <- inferTypeInContext tyctx ctx tm
    unifyType tyctx mempty ty' ty
