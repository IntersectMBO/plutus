{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes #-}

module PlutusIR.Analysis.VarInfo where

import Control.Lens hiding (Strict)
import Data.List.Extra ((!?))
import Data.Traversable
import PlutusCore qualified as PLC
import PlutusCore.Arity
import PlutusCore.Core (funTyArgs)
import PlutusCore.Name.Unique qualified as PLC
import PlutusCore.Name.UniqueMap qualified as UMap
import PlutusIR.Core

-- | Information about variables and type variables in the program.
data VarsInfo tyname name uni a = VarsInfo
  { termVarInfoMap :: PLC.UniqueMap PLC.TermUnique (VarInfo tyname name uni a)
  , typeVarInfoMap :: PLC.UniqueMap PLC.TypeUnique (TyVarInfo tyname name uni a)
  }

instance Semigroup (VarsInfo tyname name uni a) where
  (VarsInfo t ty) <> (VarsInfo t' ty') = VarsInfo (t <> t') (ty <> ty')

instance Monoid (VarsInfo tyname name uni a) where
  mempty = VarsInfo mempty mempty

-- | Lookup the 'VarInfo' for a 'name'.
lookupVarInfo
  :: PLC.HasUnique name PLC.TermUnique
  => name
  -> VarsInfo tyname name uni a
  -> Maybe (VarInfo tyname name uni a)
lookupVarInfo name (VarsInfo vim _) = UMap.lookupName name vim

-- | Lookup the 'TyVarInfo' for a 'tyname'.
lookupTyVarInfo
  :: PLC.HasUnique tyname PLC.TypeUnique
  => tyname
  -> VarsInfo tyname name uni a
  -> Maybe (TyVarInfo tyname name uni a)
lookupTyVarInfo name (VarsInfo _ vim) = UMap.lookupName name vim

-- | Information about a type variable in the program.
data TyVarInfo tyname name uni a
  = -- | A normal type variable, which could be anything.
    NormalTyVar
  | {-| A type variable corresponding to a datatype.
    Tells us the number of type variables and the constructors. -}
    DatatypeTyVar (Datatype tyname name uni a)

data VarInfo tyname name uni a
  = {-| A normal term variable, which could be anything.
    Tells us if it is strictly evaluated, its type, and possibly its arity. -}
    NormalVar Strictness (Type tyname uni a) (Maybe Arity)
  | {-| A term variable corresponding to a datatype constructor.
    Tells us the index of the constructor and the name of the datatype that owns it. -}
    DatatypeConstructor Int tyname
  | {-| A term variable corresponding to a datatype matcher.
    Tells us the name of the datatype that owns it. -}
    DatatypeMatcher tyname

varInfoStrictness :: VarInfo tyname name uni a -> Strictness
varInfoStrictness = \case
  NormalVar s _ _ -> s
  DatatypeConstructor {} -> Strict
  DatatypeMatcher {} -> Strict

varInfoArity
  :: PLC.HasUnique tyname PLC.TypeUnique
  => VarInfo tyname name uni a
  -> VarsInfo tyname name uni a
  -> Maybe Arity
varInfoArity vinfo vinfos = case vinfo of
  NormalVar _ _ a -> a
  DatatypeConstructor i dtName -> case lookupTyVarInfo dtName vinfos of
    Just (DatatypeTyVar dt) -> datatypeConstructorArity i dt
    _ -> Nothing
  DatatypeMatcher dtName -> case lookupTyVarInfo dtName vinfos of
    Just (DatatypeTyVar dt) -> Just $ datatypeMatcherArity dt
    _ -> Nothing

termVarInfo
  :: ( PLC.HasUnique name PLC.TermUnique
     , PLC.HasUnique tyname PLC.TypeUnique
     )
  => Term tyname name uni fun a
  -> VarsInfo tyname name uni a
termVarInfo = \case
  Let _ _ bs t -> foldMap bindingVarInfo bs <> termVarInfo t
  LamAbs _ n ty t ->
    VarsInfo (UMap.insertByName n (NormalVar Strict ty Nothing) mempty) mempty
      <> termVarInfo t
  TyAbs _ n _ t ->
    VarsInfo mempty (UMap.insertByName n NormalTyVar mempty)
      <> termVarInfo t
  -- No binders
  t@(Apply {}) -> foldMapOf termSubterms termVarInfo t
  t@(TyInst {}) -> foldMapOf termSubterms termVarInfo t
  t@(IWrap {}) -> foldMapOf termSubterms termVarInfo t
  t@(Unwrap {}) -> foldMapOf termSubterms termVarInfo t
  t@(Constr {}) -> foldMapOf termSubterms termVarInfo t
  t@(Case {}) -> foldMapOf termSubterms termVarInfo t
  t@(Var {}) -> foldMapOf termSubterms termVarInfo t
  t@(Constant {}) -> foldMapOf termSubterms termVarInfo t
  t@(Error {}) -> foldMapOf termSubterms termVarInfo t
  t@(Builtin {}) -> foldMapOf termSubterms termVarInfo t

datatypeMatcherArity :: Datatype tyname uni fun a -> Arity
datatypeMatcherArity (Datatype _ _ tyvars _ constrs) =
  -- One parameter for all the datatype type variables
  fmap (const TypeParam) tyvars
    -- The scrutineee, and then a type paramter for the result type
    ++ [TermParam, TypeParam]
    -- One parameter with the case for each constructor
    ++ fmap (const TermParam) constrs

datatypeConstructorArity :: Int -> Datatype tyname uni fun a -> Maybe Arity
datatypeConstructorArity i (Datatype _ _ tyvars _ constrs) =
  case constrs !? i of
    Just (VarDecl _ _ constrTy) ->
      Just $
        -- One type parameter for all of the datatype type parameters
        fmap (const TypeParam) tyvars
          -- One term parameter for all the constructor function type arguments
          ++ fmap (const TermParam) (funTyArgs constrTy)
    _ -> Nothing

bindingVarInfo
  :: ( PLC.HasUnique name PLC.TermUnique
     , PLC.HasUnique tyname PLC.TypeUnique
     )
  => Binding tyname name uni fun a
  -> VarsInfo tyname name uni a
bindingVarInfo = \case
  -- TODO: arity for term bindings
  TermBind _ s (VarDecl _ n ty) t ->
    VarsInfo (UMap.insertByName n (NormalVar s ty Nothing) mempty) mempty
      <> termVarInfo t
  TypeBind _ (TyVarDecl _ n _) _ ->
    VarsInfo mempty (UMap.insertByName n NormalTyVar mempty)
  DatatypeBind _ d@(Datatype _ (TyVarDecl _ tyname _) _ matcher constrs) ->
    let
      dtInfo =
        let info = DatatypeTyVar d
         in VarsInfo mempty (UMap.insertByName tyname info mempty)
      matcherInfo =
        let info = DatatypeMatcher tyname
         in VarsInfo (UMap.insertByName matcher info mempty) mempty
      constrInfo i (VarDecl _ n _) =
        let info = DatatypeConstructor i tyname
         in VarsInfo (UMap.insertByName n info mempty) mempty
     in
      dtInfo <> matcherInfo <> ifoldMap constrInfo constrs

-- | Get the arities of the constructors for the given datatype name.
getConstructorArities
  :: (PLC.HasUnique name PLC.TermUnique, PLC.HasUnique tyname PLC.TypeUnique)
  => tyname
  -> VarsInfo tyname name uni a
  -> Maybe [Arity]
getConstructorArities tn vinfo
  | Just (DatatypeTyVar (Datatype _ _ _ _ constrs)) <- lookupTyVarInfo tn vinfo
  , Just constrArities <- for constrs $ \c -> do
      cInfo <- lookupVarInfo (_varDeclName c) vinfo
      varInfoArity cInfo vinfo =
      Just constrArities
  | otherwise = Nothing
