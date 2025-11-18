-- editorconfig-checker-disable-file
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module PlutusIR.Core.Instance.Scoping where

import PlutusPrelude

import PlutusIR.Core.Type

import PlutusCore.Check.Scoping
import PlutusCore.MkPlc
import PlutusCore.Quote

import Data.List.NonEmpty ((<|))
import Data.List.NonEmpty qualified as NonEmpty

instance tyname ~ TyName => Reference TyName (Term tyname name uni fun) where
  referenceVia reg tyname term = TyInst NotAName term $ TyVar (reg tyname) tyname

instance name ~ Name => Reference Name (Term tyname name uni fun) where
  referenceVia reg name term = Apply NotAName term $ Var (reg name) name

instance tyname ~ TyName => Reference TyName (VarDecl tyname name uni) where
  referenceVia reg tyname (VarDecl ann varName ty) =
    VarDecl ann varName $ referenceVia reg tyname ty

{-| Scoping for data types is hard, so we employ some extra paranoia and reference the provided
'TyName' in the type of every single constructor, and also apply the final head to that 'TyName'. -}
instance tyname ~ TyName => Reference TyName (Datatype tyname name uni) where
  referenceVia reg tyname (Datatype dataAnn dataDecl params matchName constrs) =
    Datatype dataAnn dataDecl params matchName $ map goConstr constrs
    where
      tyVar = TyVar (reg tyname) tyname

      goConstr (VarDecl ann constrName constrTy) = VarDecl ann constrName $ goSpine constrTy

      goSpine (TyForall ann name kind ty) = TyForall ann name kind $ goSpine ty
      goSpine (TyFun ann dom cod) = TyFun ann dom $ goSpine cod
      goSpine ty = TyFun NotAName tyVar $ goResult ty

      goResult (TyApp ann fun arg) = TyApp ann (goResult fun) arg
      goResult ty = TyApp NotAName ty tyVar

instance tyname ~ TyName => Reference TyName (Binding tyname name uni fun) where
  referenceVia reg tyname (TermBind ann strictness varDecl term) =
    TermBind ann strictness (referenceVia reg tyname varDecl) $ referenceVia reg tyname term
  referenceVia reg tyname (TypeBind ann tyVarDecl ty) =
    TypeBind ann tyVarDecl $ referenceVia reg tyname ty
  referenceVia reg tyname (DatatypeBind ann datatype) =
    DatatypeBind ann $ referenceVia reg tyname datatype

{-| Unlike other 'Reference' instances this one does not guarantee that the name will actually be
referenced, but it's too convenient to have this instance to give up on it, without it would be
awkward to express \"reference this binding in this thing\". -}
instance name ~ Name => Reference Name (Binding tyname name uni fun) where
  referenceVia reg name (TermBind ann strictness varDecl term) =
    TermBind ann strictness varDecl $ referenceVia reg name term
  referenceVia _ _ typeBind@TypeBind {} = typeBind
  referenceVia _ _ datatypeBind@DatatypeBind {} = datatypeBind

instance Reference tyname t => Reference (TyVarDecl tyname ann) t where
  referenceVia reg = referenceVia reg . _tyVarDeclName

instance Reference name t => Reference (VarDecl tyname name uni ann) t where
  referenceVia reg = referenceVia reg . _varDeclName

instance (Reference TyName t, Reference Name t) => Reference (Datatype TyName Name uni ann) t where
  referenceVia reg (Datatype _ dataDecl params matchName constrs) =
    referenceVia reg dataDecl
      -- Parameters of a data type are not visible outside of the data type no matter what.
      . referenceOutOfScope params
      . referenceVia reg matchName
      . referenceVia reg constrs

instance (Reference TyName t, Reference Name t) => Reference (Binding TyName Name uni fun ann) t where
  referenceVia reg (TermBind _ _ varDecl _) = referenceVia reg varDecl
  referenceVia reg (TypeBind _ tyVarDecl _) = referenceVia reg tyVarDecl
  referenceVia reg (DatatypeBind _ datatype) = referenceVia reg datatype

{-| Establish scoping for each of the parameters of a datatype by only annotating every parameter
with 'introduceBound'. -}
establishScopingParams :: [TyVarDecl TyName ann] -> Quote [TyVarDecl TyName NameAnn]
establishScopingParams =
  traverse $ \(TyVarDecl _ paramNameDup paramKind) -> do
    paramName <- freshenTyName paramNameDup
    TyVarDecl (introduceBound paramName) paramName <$> establishScoping paramKind

-- See Note [Weird IR data types].
{-| Establish scoping for the type of a constructor. The updated constructor expects an argument
of the \"the data type applied to all its parameters\" type (that argument is the last one) and
always returns that exact type as a result. For example, this functions turns the following
generated type of constructor

    integer -> a -> <a_non_->_type>

into

    integer -> a -> D a b -> D a b

assuming the constructor is supposed to construct a data type @D@ parameterized by two parameters
@a@ and @b@. Note that @<a_non_->_type>@ can be anything as the generator is allowed to generate
mess such as a constructor not actually constructing a value of the data type.

Whether the name of the data type is referenced as in-scope or out-of-scope one in the types of
arguments of constructors is controlled by the first argument, which ultimately depends on the
recursivity of the data type. -}
establishScopingConstrTy
  :: (TyName -> NameAnn)
  -> TyName
  -> [TyVarDecl TyName NameAnn]
  -> Type TyName uni ann
  -> Quote (Type TyName uni NameAnn)
establishScopingConstrTy regSelf dataName params = goSpine
  where
    toDataAppliedToParams reg =
      mkIterTyApp (TyVar (reg dataName) dataName) $
        map (\(TyVarDecl _ name _) -> (NotAName, TyVar (registerBound name) name)) params

    goSpine (TyForall _ nameDup kindDup ty) = do
      -- Similar to 'establishScopingBinder', but uses 'TyFun' rather than whatever 'registerVia'
      -- uses in order not to break the invariants described in Note [Weird IR data types].
      -- Also calls 'goSpine' recursively rather than 'establishScoping'.
      name <- freshenTyName nameDup
      kind <- establishScoping kindDup
      TyFun NotAName (TyVar (registerOutOfScope name) name)
        . TyForall (introduceBound name) name kind
        . TyFun NotAName (TyVar (registerBound name) name)
        <$> goSpine ty
    goSpine (TyFun _ dom cod) = TyFun NotAName <$> establishScoping dom <*> goSpine cod
    goSpine _ =
      pure . TyFun NotAName (toDataAppliedToParams regSelf) $ toDataAppliedToParams registerBound

{-| Establish scoping for all constructors of a data type by establishing scoping for each of them
individually. If there are no constructors, then a dummy one is added, because we need to
maintain the invariant that every binding is referenced as an in-scope one somewhere and the only
place where parameters of a data type can be referenced this way is a constructor of that data
type. -}
establishScopingConstrs
  :: (TyName -> NameAnn)
  -> ann
  -> TyName
  -> [TyVarDecl TyName NameAnn]
  -> [VarDecl TyName Name uni ann]
  -> Quote [VarDecl TyName Name uni NameAnn]
establishScopingConstrs regSelf dataAnn dataName params constrsPossiblyEmpty = do
  cons0Name <- freshName "cons0"
  let cons0 = VarDecl dataAnn cons0Name $ TyVar dataAnn dataName
      constrs = if null constrsPossiblyEmpty then [cons0] else constrsPossiblyEmpty
  for constrs $ \(VarDecl _ constrNameDup constrTyDup) -> do
    constrName <- freshenName constrNameDup
    constrTy <- establishScopingConstrTy regSelf dataName params constrTyDup
    pure $ VarDecl (introduceBound constrName) constrName constrTy

{-| Establish scoping of a binding. Each bindings gets referenced in its own body either as an
in-scope or out-of-scope one, which is controlled by the first argument and ultimately depends on
the recursivity of the binding. -}
establishScopingBinding
  :: (forall name. ToScopedName name => name -> NameAnn)
  -> Binding TyName Name uni fun ann
  -> Quote (Binding TyName Name uni fun NameAnn)
establishScopingBinding regSelf (TermBind _ strictness (VarDecl _ nameDup ty) term) = do
  name <- freshenName nameDup
  varDecl <- VarDecl (introduceBound name) name <$> establishScoping ty
  TermBind NotAName strictness varDecl . referenceVia regSelf name <$> establishScoping term
establishScopingBinding regSelf (TypeBind _ (TyVarDecl _ nameDup kind) ty) = do
  name <- freshenTyName nameDup
  tyVarDecl <- TyVarDecl (introduceBound name) name <$> establishScoping kind
  TypeBind NotAName tyVarDecl . referenceVia regSelf name <$> establishScoping ty
establishScopingBinding regSelf (DatatypeBind dataAnn datatypeDup) = do
  let Datatype _ dataDeclDup paramsDup matchNameDup constrsDup = datatypeDup
      TyVarDecl _ dataNameDup dataKind = dataDeclDup
  dataName <- freshenTyName dataNameDup
  dataDecl <- TyVarDecl (introduceBound dataName) dataName <$> establishScoping dataKind
  params <- establishScopingParams paramsDup
  matchName <- freshenName matchNameDup
  constrs <- establishScopingConstrs regSelf dataAnn dataName params constrsDup
  let datatype = Datatype (introduceBound matchName) dataDecl params matchName constrs
  pure $ DatatypeBind NotAName datatype

-- | Reference each binding in the last one apart from itself.
referenceViaBindings
  :: (forall name. ToScopedName name => name -> NameAnn)
  -> NonEmpty (Binding TyName Name uni fun NameAnn)
  -> NonEmpty (Binding TyName Name uni fun NameAnn)
referenceViaBindings _ (b0 :| []) = b0 :| []
referenceViaBindings reg (b0 :| bs0) = go [] b0 bs0
  where
    go prevs b [] = referenceVia reg prevs b :| []
    go prevs b (c : bs) = b <| go (b : prevs) c bs

{-| Reference each binding in the first one apart from itself and in the last one also apart from
itself. Former bindings are always visible in latter ones and whether latter bindings are visible
in former ones is controlled by the first argument and ultimately depends on the recursivity
of the family of bindings. -}
referenceBindingsBothWays
  :: (forall name. ToScopedName name => name -> NameAnn)
  -> NonEmpty (Binding TyName Name uni fun NameAnn)
  -> NonEmpty (Binding TyName Name uni fun NameAnn)
referenceBindingsBothWays regRec -- Whether latter bindings are visible in former ones
  =
  NonEmpty.reverse -- or not depends on the recursivity and so we have
    . referenceViaBindings regRec -- the registering function as an argument.
    . NonEmpty.reverse
    . referenceViaBindings registerBound -- Former bindings are always visible in latter ones.

-- | Establish scoping for a family of bindings.
establishScopingBindings
  :: (forall name. ToScopedName name => name -> NameAnn)
  -> NonEmpty (Binding TyName Name uni fun ann)
  -> Quote (NonEmpty (Binding TyName Name uni fun NameAnn))
establishScopingBindings regRec =
  -- Note that mutual recursion and self-recursion are handled separately.
  fmap (referenceBindingsBothWays regRec) . traverse (establishScopingBinding regRec)

-- | Return a registering function depending on the recursivity.
registerByRecursivity :: ToScopedName name => Recursivity -> name -> NameAnn
registerByRecursivity Rec = registerBound
registerByRecursivity NonRec = registerOutOfScope

firstBound :: Term tyname name uni fun ann -> [name]
firstBound (Apply _ (LamAbs _ name _ body) _) = name : firstBound body
firstBound _ = []

instance (tyname ~ TyName, name ~ Name) => EstablishScoping (Term tyname name uni fun) where
  establishScoping (Let _ recy bindingsDup body) = do
    bindings <- establishScopingBindings (registerByRecursivity recy) bindingsDup
    -- Follows the shape of 'establishScopingBinder', but subtly differs (for example,
    -- does not bind a single name, does not have a @sort@ etc), hence we write things out
    -- manually.
    referenceOutOfScope bindings
      . Let NotAName recy bindings
      . referenceBound bindings
      <$> establishScoping body
  establishScoping (LamAbs _ nameDup ty body) = do
    name <- freshenName nameDup
    establishScopingBinder LamAbs name ty body
  establishScoping (TyAbs _ nameDup kind body) = do
    name <- freshenTyName nameDup
    establishScopingBinder TyAbs name kind body
  establishScoping (IWrap _ pat arg term) =
    IWrap NotAName <$> establishScoping pat <*> establishScoping arg <*> establishScoping term
  establishScoping (Apply _ fun arg) =
    Apply NotAName <$> establishScoping fun <*> establishScoping arg
  establishScoping (Unwrap _ term) = Unwrap NotAName <$> establishScoping term
  establishScoping (Error _ ty) = Error NotAName <$> establishScoping ty
  establishScoping (TyInst _ term ty) =
    TyInst NotAName <$> establishScoping term <*> establishScoping ty
  establishScoping (Var _ nameDup) = do
    name <- freshenName nameDup
    pure $ Var (registerFree name) name
  establishScoping (Constant _ con) = pure $ Constant NotAName con
  establishScoping (Builtin _ bi) = pure $ Builtin NotAName bi
  establishScoping (Constr _ ty i es) = Constr NotAName <$> establishScoping ty <*> pure i <*> traverse establishScoping es
  establishScoping (Case _ ty a es) = do
    esScoped <- traverse establishScoping es
    let esScopedPoked = addTheRest $ map (\e -> (e, firstBound e)) esScoped
        branchBounds = map (snd . fst) esScopedPoked
        referenceInBranch ((branch, _), others) = referenceOutOfScope (map snd others) branch
    tyScoped <- establishScoping ty
    aScoped <- establishScoping a
    -- For each of the branches reference (as out-of-scope) the variables bound in that branch
    -- in all the other ones, as well as outside of the whole case-expression. This is to check
    -- that none of the transformations leak variables outside of the branch they're bound in.
    pure . referenceOutOfScope branchBounds $
      Case NotAName tyScoped aScoped $
        map referenceInBranch esScopedPoked

instance (tyname ~ TyName, name ~ Name) => EstablishScoping (Program tyname name uni fun) where
  establishScoping (Program _ v term) = Program NotAName v <$> establishScoping term

instance tyname ~ TyName => CollectScopeInfo (TyVarDecl tyname) where
  collectScopeInfo (TyVarDecl ann tyname kind) = handleSname ann tyname <> collectScopeInfo kind

instance (tyname ~ TyName, name ~ Name) => CollectScopeInfo (VarDecl tyname name uni) where
  collectScopeInfo (VarDecl ann name ty) = handleSname ann name <> collectScopeInfo ty

instance (tyname ~ TyName, name ~ Name) => CollectScopeInfo (Datatype tyname name uni) where
  collectScopeInfo (Datatype matchAnn dataDecl params matchName constrs) =
    fold
      [ collectScopeInfo dataDecl
      , foldMap collectScopeInfo params
      , handleSname matchAnn matchName
      , foldMap collectScopeInfo constrs
      ]

instance (tyname ~ TyName, name ~ Name) => CollectScopeInfo (Binding tyname name uni fun) where
  collectScopeInfo (TermBind _ _ varDecl term) = collectScopeInfo varDecl <> collectScopeInfo term
  collectScopeInfo (TypeBind _ tyVarDecl ty) = collectScopeInfo tyVarDecl <> collectScopeInfo ty
  collectScopeInfo (DatatypeBind _ datatype) = collectScopeInfo datatype

instance (tyname ~ TyName, name ~ Name) => CollectScopeInfo (Term tyname name uni fun) where
  collectScopeInfo (Let _ _ bindings body) =
    foldMap collectScopeInfo bindings <> collectScopeInfo body
  collectScopeInfo (LamAbs ann name ty body) =
    handleSname ann name <> collectScopeInfo ty <> collectScopeInfo body
  collectScopeInfo (TyAbs ann name kind body) =
    handleSname ann name <> collectScopeInfo kind <> collectScopeInfo body
  collectScopeInfo (IWrap _ pat arg term) =
    collectScopeInfo pat <> collectScopeInfo arg <> collectScopeInfo term
  collectScopeInfo (Apply _ fun arg) = collectScopeInfo fun <> collectScopeInfo arg
  collectScopeInfo (Unwrap _ term) = collectScopeInfo term
  collectScopeInfo (Error _ ty) = collectScopeInfo ty
  collectScopeInfo (TyInst _ term ty) = collectScopeInfo term <> collectScopeInfo ty
  collectScopeInfo (Var ann name) = handleSname ann name
  collectScopeInfo (Constant _ _) = mempty
  collectScopeInfo (Builtin _ _) = mempty
  collectScopeInfo (Constr _ ty _ es) = collectScopeInfo ty <> foldMap collectScopeInfo es
  collectScopeInfo (Case _ ty arg cs) = collectScopeInfo ty <> collectScopeInfo arg <> foldMap collectScopeInfo cs

instance (tyname ~ TyName, name ~ Name) => CollectScopeInfo (Program tyname name uni fun) where
  collectScopeInfo (Program _ _ term) = collectScopeInfo term
