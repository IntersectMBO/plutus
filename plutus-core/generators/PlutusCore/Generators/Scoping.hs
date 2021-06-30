{-# LANGUAGE RankNTypes   #-}
{-# LANGUAGE TypeFamilies #-}

module PlutusCore.Generators.Scoping where

import           PlutusCore
import           PlutusCore.Quote

import           Control.Monad.Except
import           Control.Monad.Reader
import           Data.Set                    as Set

import           PlutusCore.StdLib.Data.List

data Scope name = Scope
   { _inScope    :: Set name
   , _notInScope :: Set name
   }

data Scopes = Scopes
    { _scopesType :: Scope TyName
    , _scopesTerm :: Scope Name
    }

emptyScope :: Scope name
emptyScope = Scope Set.empty Set.empty

emptyScopes :: Scopes
emptyScopes = Scopes emptyScope emptyScope

-- free stays
-- binding disappears
-- bound disappears
-- invisible added as free stays
data ScopeDelta
    = Stays (Either TyName Name)
    | Disappears (Either TyName Name)
    | NoChange
    deriving (Show)

class Scoping t where
    scoping :: t () -> t ScopeDelta

introduceBound :: Either TyName Name -> ScopeDelta
introduceBound = Disappears

-- registerBound :: Either TyName Name -> ScopeDelta
-- registerBound = NoChange

registerFree :: Either TyName Name -> ScopeDelta
registerFree = Stays

-- referenceTyName :: TyName -> Type TyName uni ScopeDelta -> Type TyName uni ScopeDelta
-- referenceTyName tyname = TyFun NoChange $ TyVar (registerBound $ Left tyname) tyname

referenceTyName :: TyName -> Type TyName uni ScopeDelta -> Type TyName uni ScopeDelta
referenceTyName tyname = TyFun NoChange $ TyVar NoChange tyname

-- establishScoping
instance tyname ~ TyName => Scoping (Type tyname uni) where
    scoping (TyLam _ name kind ty) =
        TyLam (introduceBound $ Left name) name (NoChange <$ kind) $
            referenceTyName name $ scoping ty
    scoping (TyForall _ name kind ty) =
        TyForall (introduceBound $ Left name) name (NoChange <$ kind) $
            referenceTyName name $ scoping ty
    scoping (TyIFix _ pat arg) = TyIFix NoChange (scoping pat) (scoping arg)
    scoping (TyApp _ fun arg) = TyApp NoChange (scoping fun) (scoping arg)
    scoping (TyFun _ dom cod) = TyFun NoChange (scoping dom) (scoping cod)
    scoping (TyVar _ name) = TyVar (registerFree $ Left name) name
    scoping (TyBuiltin _ fun) = TyBuiltin NoChange fun

-- 'deepOf' :: 'Traversal'' s s    -> 'Traversal'' s a             -> 'Traversal'' s a
-- deepOf :: 'Traversal' s t s t -> 'Traversal' s t a b          -> 'Traversal' s t a b

-- >>> :set -XTypeApplications
-- >>> runScopeM . checkScoping . runQuote . rename . scoping $ dissociateType @DefaultUni listTy
-- Right ()


-- >>> :set -XTypeApplications
-- >>> runQuote . rename . scoping $ dissociateType @DefaultUni listTy
-- TyLam (Disappears (Left (TyName {unTyName = Name {nameString = "a", nameUnique = Unique {unUnique = 0}}}))) (TyName {unTyName = Name {nameString = "a", nameUnique = Unique {unUnique = 11}}}) (Type NoChange) (TyIFix NoChange (TyLam (Disappears (Left (TyName {unTyName = Name {nameString = "list", nameUnique = Unique {unUnique = 1}}}))) (TyName {unTyName = Name {nameString = "list", nameUnique = Unique {unUnique = 12}}}) (KindArrow NoChange (Type NoChange) (Type NoChange)) (TyLam (Disappears (Left (TyName {unTyName = Name {nameString = "a", nameUnique = Unique {unUnique = 2}}}))) (TyName {unTyName = Name {nameString = "a", nameUnique = Unique {unUnique = 13}}}) (Type NoChange) (TyForall (Disappears (Left (TyName {unTyName = Name {nameString = "r", nameUnique = Unique {unUnique = 3}}}))) (TyName {unTyName = Name {nameString = "r", nameUnique = Unique {unUnique = 14}}}) (Type NoChange) (TyFun NoChange (TyVar (Disappears (Left (TyName {unTyName = Name {nameString = "r", nameUnique = Unique {unUnique = 3}}}))) (TyName {unTyName = Name {nameString = "r", nameUnique = Unique {unUnique = 14}}})) (TyFun NoChange (TyVar (Stays (Left (TyName {unTyName = Name {nameString = "r", nameUnique = Unique {unUnique = 4}}}))) (TyName {unTyName = Name {nameString = "r", nameUnique = Unique {unUnique = 4}}})) (TyFun NoChange (TyFun NoChange (TyVar (Stays (Left (TyName {unTyName = Name {nameString = "a", nameUnique = Unique {unUnique = 5}}}))) (TyName {unTyName = Name {nameString = "a", nameUnique = Unique {unUnique = 5}}})) (TyFun NoChange (TyApp NoChange (TyVar (Stays (Left (TyName {unTyName = Name {nameString = "list", nameUnique = Unique {unUnique = 6}}}))) (TyName {unTyName = Name {nameString = "list", nameUnique = Unique {unUnique = 6}}})) (TyVar (Stays (Left (TyName {unTyName = Name {nameString = "a", nameUnique = Unique {unUnique = 7}}}))) (TyName {unTyName = Name {nameString = "a", nameUnique = Unique {unUnique = 7}}}))) (TyVar (Stays (Left (TyName {unTyName = Name {nameString = "r", nameUnique = Unique {unUnique = 8}}}))) (TyName {unTyName = Name {nameString = "r", nameUnique = Unique {unUnique = 8}}})))) (TyVar (Stays (Left (TyName {unTyName = Name {nameString = "r", nameUnique = Unique {unUnique = 9}}}))) (TyName {unTyName = Name {nameString = "r", nameUnique = Unique {unUnique = 9}}})))))))) (TyVar (Stays (Left (TyName {unTyName = Name {nameString = "a", nameUnique = Unique {unUnique = 10}}}))) (TyName {unTyName = Name {nameString = "a", nameUnique = Unique {unUnique = 10}}})))
dissociateType :: Type TyName uni ann -> Type TyName uni ann
dissociateType = runQuote . go where
    go (TyLam ann name kind ty) = do
        nameFr <- freshenTyName name
        TyLam ann nameFr kind <$> go ty
    go (TyForall ann name kind ty) = do
        nameFr <- freshenTyName name
        TyForall ann nameFr kind <$> go ty
    go (TyIFix ann pat arg) = TyIFix ann <$> go pat <*> go arg
    go (TyApp ann fun arg) = TyApp ann <$> go fun <*> (go arg)
    go (TyFun ann dom cod) = TyFun ann <$> go dom <*> go cod
    go (TyVar ann name) = TyVar ann <$> freshenTyName name
    go (TyBuiltin ann fun) = pure $ TyBuiltin ann fun

data ScopingError
    = SupposedToBeInScope (Either TyName Name)
    | NotSupposedToBeInScope (Either TyName Name)
    | NotSupposedToBeNotInScope (Either TyName Name)
    | FreeVariableRenamed (Either TyName Name)
    deriving (Show)

type ScopeM = ReaderT Scopes (Either ScopingError)

runScopeM :: ScopeM a -> Either ScopingError a
runScopeM = flip runReaderT emptyScopes

class CheckScoping t where
    checkScoping :: t ScopeDelta -> ScopeM ()

applyStays :: Ord name => name -> Scope name -> Scope name
applyStays name (Scope inScope notInScope) = Scope (Set.insert name inScope) notInScope

applyDisappears :: Ord name => name -> Scope name -> Scope name
applyDisappears name (Scope inScope notInScope) = Scope inScope (Set.insert name notInScope)

pickScopeAnd
    :: (forall name. Ord name => name -> Scope name -> Scope name)
    -> Either TyName Name
    -> Scopes
    -> Scopes
pickScopeAnd f (Left tyname) (Scopes typeScope termScope) = Scopes (f tyname typeScope) termScope
pickScopeAnd f (Right name)  (Scopes typeScope termScope) = Scopes typeScope (f name termScope)

applyScopeDelta :: ScopeDelta -> Scopes -> Scopes
applyScopeDelta (Stays      ename) = pickScopeAnd applyStays      ename
applyScopeDelta (Disappears ename) = pickScopeAnd applyDisappears ename
applyScopeDelta NoChange           = id

withScopeDelta :: ScopeDelta -> ScopeM a -> ScopeM a
withScopeDelta = withReaderT . applyScopeDelta

-- if appears then in scope VS has to appear

-- bound => notInScope => can't appear
-- stays => free => annotation equals name

checkScopingName :: Ord name => (name -> Either TyName Name) -> name -> Scope name -> ScopeM ()
checkScopingName emb name (Scope inScope notInScope) = do
    unless (name `Set.member` inScope) $ throwError . SupposedToBeInScope $ emb name
    unless (name `Set.notMember` notInScope) $ throwError . NotSupposedToBeInScope $ emb name

checkScopingName' :: Ord name => (name -> Either TyName Name) -> name -> Scope name -> ScopeM ()
checkScopingName' emb name (Scope inScope notInScope) = do
    unless (name `Set.notMember` inScope) $ throwError . NotSupposedToBeInScope $ emb name
    unless (name `Set.notMember` notInScope) $ throwError . NotSupposedToBeNotInScope $ emb name

-- stays      => old equals new, sanity: old in old scope, old not notIn old scope
-- disappears => old not in old scope, new not in old scope, new not notIn old scope

-- \x_1 -> x_2
-- \@(disappears x_1) x_1 -> @(disappears x_1) x_1 -> @(stays x_2) x_2
-- \@(disappears x_1) x_3 -> @(disappears x_1) x_3 -> @(stays x_2) x_2

-- \@(add x_1 to notInScope, x_3 must not be anywhere) x_3 -> @(x_1 must not be in inScope, must be in notInScope, x_3 must not to be anywhere) x_3 -> @(annotation x_2 must be equal to the variable, must not be in inScope, must not be in notInScope) x_2

-- checkScoping:
-- \@(add x_1 to notInScope, x_3 must not be in notInScope) x_3 -> @(x_1 must be in notInScope, x_3 must not be in notInScope) x_3 -> @(annotation x_2 must be equal to the variable, x_2 must not be in notInScope) x_2

-- wrong:
-- \x_2 -> x_* -> x_2  -- bound renamed to free -- not caught!
-- \x_1 -> x_* -> x_3  -- free changed
-- \x_3 -> x_1 -> x_2  -- bound renamed at introduction site but not use site

-- let nonrec x_1 = {- x_1 not visible in -} x_2 in x_3

-- let nonrec x_1 = x_1 -> x_2 in x_1 -> x_3

-- let nonrec @(disappears_binding x_1) x_1 = @(stays_out_of_scope x_1) x_1 -> @(stays_free x_2) x_2 in @(disappears_bound x_1) x_1 -> @(stays_free x_3) x_3

-- let nonrec @(disappears_binding x_1) x_4 = @(stays_out_of_scope x_1) x_1 -> @(stays_free x_2) x_2 in @(disappears_bound x_1) x_4 -> @(stays_free x_3) x_3

-- definition vs usage

-- @(disappears_binding x_1) x_4: x_1 must not be equal to x_4, x_1 is added to d_notInScope, x_4 is added to d_inScope
-- @(stays_out_of_scope x_1) x_1: x_1 must be equal to x_1, x_1 is added to u_outOfScope
-- @(stays_free x_2) x_2: x_2 must be equal to x_2, x_2 is added to u_notInScope


-- let nonrec x_1 = x_2 in x_3

-- let nonrec @(disappears_binding x_1) x_1 = @(stays_out_of_scope x_1) x_1 -> @(stays_free x_2) x_2 in @(disappears_bound x_1) x_1 -> @(stays_free x_3) x_3

-- let nonrec @(disappears_binding x_1) x_4 = @(stays_out_of_scope x_1) x_1 -> @(stays_free x_2) x_2 in @(disappears_bound x_1) x_4 -> @(stays_free x_3) x_3

-- @(disappears_binding x_1) x_4: x_1 must not be equal to x_4, x_1 is added to out_of_scope, x_4 is added to in_scope
-- @(stays_out_of_scope x_1) x_1: x_1 must be equal to x_1, x_1 must be in out_of_scope, x_1 must not be in in_scope
-- @(stays_free x_2) x_2: x_2 must be equal to x_2, x_2 must not be in out_of_scope, x_2 must not be in in_scope
-- @(disappears_bound x_1) x_4: x_1 must not be equal to x_4, x_1 must be in out_of_scope, x_4 must be in in_scope
-- @(stays_free x_3) x_3: x_3 must be equal to x_3, x_3 must not be in out_of_scope, x_3 must not be in in_scope

-- free variables
-- out of scope variables
-- disappeared bindings
-- disappeared variables

-- let y = (let x = a in b) in c
-- let y = (let x = a in b) in @out_of_scope x + c  -- ill-scoped


-- let nonrec @(add x_1 to notInScope, x_4 must not be in notInScope) x_4 = x_1 -> x_2 in x_4 -> x_3

checkScopingVar :: ScopeDelta -> Either TyName Name -> ScopeM ()
checkScopingVar NoChange ename = do
    Scopes typeScope termScope <- ask
    case ename of
        Left tyname -> checkScopingName' Left  tyname typeScope
        Right name  -> checkScopingName' Right name   termScope
checkScopingVar delta    ename = do
    Scopes typeScope termScope <- ask
    case ename of
        Left tyname -> checkScopingName Left  tyname typeScope
        Right name  -> checkScopingName Right name   termScope
    case delta of
        -- One free variable was renamed to another one.
        Stays ename'      -> unless (ename == ename') . throwError $ FreeVariableRenamed ename
        -- This should be caught via checking the not-in-scope part, but whatever.
        Disappears ename2 -> unless (ename /= ename2) $ error "Something horribly wrong has happened: a variable is verified not to be in scope, yet it somehow equals the original in-scope variable"
        NoChange          -> pure ()

instance tyname ~ TyName => CheckScoping (Type tyname uni) where
    checkScoping ty0 = withScopeDelta (typeAnn ty0) $ case ty0 of
        TyLam _ _ _ ty    -> checkScoping ty
        TyForall _ _ _ ty -> checkScoping ty
        TyIFix _ pat arg  -> checkScoping pat *> checkScoping arg
        TyApp _ fun arg   -> checkScoping fun *> checkScoping arg
        TyFun _ dom cod   -> checkScoping dom *> checkScoping cod
        TyVar delta name  -> checkScopingVar delta $ Left name
        TyBuiltin _ _     -> pure ()
