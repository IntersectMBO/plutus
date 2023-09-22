{-# LANGUAGE LambdaCase     #-}
{-# LANGUAGE NamedFieldPuns #-}
module PlutusIR.Analysis.VarInfo where

import Control.Lens hiding (Strict)
import PlutusCore.Core (funTyArgs)
import PlutusCore.Core qualified as PLC
import PlutusCore.Name qualified as PLC
import PlutusIR.Core
import Prettyprinter

-- | Information about variables and type variables in the program.
data VarsInfo tyname name = VarsInfo
  { termVarInfoMap :: PLC.UniqueMap PLC.TermUnique (VarInfo tyname name)
  , typeVarInfoMap :: PLC.UniqueMap PLC.TypeUnique (TyVarInfo tyname name)
  }

instance Semigroup (VarsInfo tyname name) where
  (VarsInfo t ty) <> (VarsInfo t' ty') = VarsInfo (t <> t') (ty <> ty')

instance Monoid (VarsInfo tyname name) where
  mempty = VarsInfo mempty mempty

-- | Lookup the 'VarInfo' for a 'name'.
lookupVarInfo ::
  (PLC.HasUnique name PLC.TermUnique)
  => name
  -> VarsInfo tyname name
  -> Maybe (VarInfo tyname name)
lookupVarInfo name (VarsInfo vim _) = PLC.lookupName name vim

-- | Lookup the 'TyVarInfo' for a 'tyname'.
lookupTyVarInfo ::
  (PLC.HasUnique tyname PLC.TypeUnique)
  => tyname
  -> VarsInfo tyname name
  -> Maybe (TyVarInfo tyname name)
lookupTyVarInfo name (VarsInfo _ vim) = PLC.lookupName name vim

-- | Information about a type variable in the program.
data TyVarInfo tyname name =
  -- | A normal type variable, which could be anything.
  NormalTyVar
  -- | A type variable corresponding to a datatype.
  -- Tells us the number of type variables and the constructors.
  | DatatypeTyVar Int [name]

data VarInfo tyname name =
  -- | A normal term variable, which could be anything.
  -- Tells us if it is strictly evaluated, and possibly its arity.
  NormalVar Strictness (Maybe Arity)
  -- | A term variable corresponding to a datatype constructor.
  -- Tells us the arity and the name of the datatype that owns it.
  | DatatypeConstructor Arity tyname
  -- | A term variable corresponding to a datatype matcher.
  -- Tells us the arity and the name of the datatype that owns it.
  | DatatypeMatcher Arity tyname

-- | Is the next argument a term or a type?
data Param =
    TermParam | TypeParam
    deriving stock (Show)

instance Pretty Param where
  pretty = viaShow

{-|
The (syntactic) arity of a term. That is, a record of the arguments that the
term expects before it may do some work. Since we have both type and lambda
abstractions, this is not a simple argument count, but rather a list of values
indicating whether the next argument should be a term or a type.

Note that this is the syntactic arity, i.e. it just corresponds to the number of
syntactic lambda and type abstractions on the outside of the term. It is thus
an under-approximation of how many arguments the term may need.
e.g. consider the term @let id = \x -> x in id@: the variable @id@ has syntactic
arity @[]@, but does in fact need an argument before it does any work.
-}
type Arity = [Param]

varInfoStrictness :: VarInfo tyname name -> Strictness
varInfoStrictness = \case
  NormalVar s _         -> s
  DatatypeConstructor{} -> Strict
  DatatypeMatcher{}     -> Strict

varInfoArity :: VarInfo tyname name -> Maybe Arity
varInfoArity = \case
  NormalVar _ a           -> a
  DatatypeConstructor a _ -> Just a
  DatatypeMatcher a _     -> Just a

termVarInfo ::
  (PLC.HasUnique name PLC.TermUnique
  , PLC.HasUnique tyname PLC.TypeUnique)
  => Term tyname name uni fun a
  -> VarsInfo tyname name
termVarInfo = \case
  Let _ _ bs t   -> foldMap bindingVarInfo bs <> termVarInfo t
  LamAbs _ n _ t ->
    VarsInfo (PLC.insertByName n (NormalVar Strict Nothing) mempty) mempty
    <> termVarInfo t
  TyAbs _ n _ t   ->
    VarsInfo mempty (PLC.insertByName n NormalTyVar mempty)
    <> termVarInfo t
  -- No binders
  t@(Apply{})    -> foldMapOf termSubterms termVarInfo t
  t@(TyInst{})   -> foldMapOf termSubterms termVarInfo t
  t@(IWrap{})    -> foldMapOf termSubterms termVarInfo t
  t@(Unwrap{})   -> foldMapOf termSubterms termVarInfo t
  t@(Constr{})   -> foldMapOf termSubterms termVarInfo t
  t@(Case{})     -> foldMapOf termSubterms termVarInfo t
  t@(Var{})      -> foldMapOf termSubterms termVarInfo t
  t@(Constant{}) -> foldMapOf termSubterms termVarInfo t
  t@(Error{})    -> foldMapOf termSubterms termVarInfo t
  t@(Builtin{})  -> foldMapOf termSubterms termVarInfo t

bindingVarInfo ::
  (PLC.HasUnique name PLC.TermUnique
  , PLC.HasUnique tyname PLC.TypeUnique)
  => Binding tyname name uni fun a
  -> VarsInfo tyname name
bindingVarInfo = \case
  -- TODO: arity for term bindings
  TermBind _ s (VarDecl _ n _) t ->
    VarsInfo (PLC.insertByName n (NormalVar s Nothing) mempty) mempty
    <> termVarInfo t
  TypeBind _ (TyVarDecl _ n _) _ ->
    VarsInfo mempty (PLC.insertByName n NormalTyVar mempty)
  DatatypeBind _ (Datatype _ (TyVarDecl _ tyname _) tyvars matcher constrs) ->
    let
      dtInfo =
        let info = DatatypeTyVar (length tyvars) (fmap (view PLC.varDeclName) constrs)
        in VarsInfo mempty (PLC.insertByName tyname info mempty)
      matcherArity =
        -- One parameter for all the datatype type variables
        fmap (const TypeParam) tyvars
        -- The scrutineee, and then a type paramter for the result type
        ++ [TermParam, TypeParam]
        -- One parameter with the case for each constructor
        ++ fmap (const TermParam) constrs
      matcherInfo =
        let info = DatatypeMatcher matcherArity tyname
        in VarsInfo (PLC.insertByName matcher info mempty) mempty
      constrArity constrTy =
        -- One parameter for all function type arguments
        fmap (const TypeParam) (funTyArgs constrTy)
      constrInfo (VarDecl _ n ty) =
        let info = DatatypeConstructor (constrArity ty) tyname
        in VarsInfo (PLC.insertByName n info mempty) mempty
    in dtInfo <> matcherInfo <> foldMap constrInfo constrs
