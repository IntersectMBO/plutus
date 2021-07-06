{-# LANGUAGE RankNTypes        #-}
{-# LANGUAGE TypeFamilies      #-}

{-# LANGUAGE OverloadedStrings #-}

module PlutusCore.Generators.Scoping where

import           PlutusCore
import           PlutusCore.Name
import           PlutusCore.Quote

import           Control.Monad.Except
import           Control.Monad.Reader
import           Data.Coerce
import           Data.Either
import           Data.Map.Strict             as Map
import           Data.Maybe
import           Data.Set                    as Set

import           PlutusCore.StdLib.Data.List

-- let nonrec x_1 = x_2 in x_3

-- let nonrec @(disappears_binding x_1) x_1 = @(stays_out_of_scope x_1) x_1 -> @(stays_free x_2) x_2 in @(disappears_bound x_1) x_1 -> @(stays_free x_3) x_3

-- let nonrec @(disappears_binding x_1) x_4 = @(stays_out_of_scope x_1) x_1 -> @(stays_free x_2) x_2 in @(disappears_bound x_1) x_4 -> @(stays_free x_3) x_3

-- @(disappears_binding x_1) x_4: x_1 must not be equal to x_4, x_1 is added to out_of_scope, x_4 is added to in_scope
-- @(stays_out_of_scope x_1) x_1: x_1 must be equal to x_1, x_1 must be in out_of_scope, x_1 must not be in in_scope
-- @(stays_free x_2) x_2: x_2 must be equal to x_2, x_2 must not be in out_of_scope, x_2 must not be in in_scope
-- @(disappears_bound x_1) x_4: x_1 must not be equal to x_4, x_1 must be in out_of_scope, x_4 must be in in_scope
-- @(stays_free x_3) x_3: x_3 must be equal to x_3, x_3 must not be in out_of_scope, x_3 must not be in in_scope



-- let nonrec x_1 = x_2 in x_3
-- let nonrec x_1 = x_2 in let nonrec x_1 = x_2 in x_3  -- Duplicating a binding makes the duplicate disappear


-- \x_1 -> x_2
-- x_1 (\x_1 -> x_1 x_2)
-- @(stays_out_of_scope x_1) x_1 (\(@disappears_binding x_1) x_1 -> @(disappears_var x_1) x_1 @(stays_free x_2) x_2)
-- @(stays_out_of_scope x_1) x_1 (\(@disappears_binding x_1) x_3 -> @(disappears_var x_1) x_3 @(stays_free x_2) x_2)

data Persists
    = StaysOutOfScopeVariable
    | StaysFreeVariable
    deriving (Show)

data Changes
    = DisappearsBinding
    | DisappearsVariable
    deriving (Show)

-- data Disappears
--     = DisappearsBinding
--     | DisappearsVariable
--     deriving (Show)

-- data Appears
--     = AppearsBinding
--     | AppearsVariable
--     deriving (Show)

data NameAction
    = Persists Persists
    | Changes Changes
    -- | Disappears Disappears
    -- | Appears Appears
    deriving (Show)

data NameAnnotation
    = NameAction NameAction (Either TyName Name)
    | NotAName
    deriving (Show)

introduceBound :: Either TyName Name -> NameAnnotation
introduceBound = NameAction $ Changes DisappearsBinding

registerBound :: Either TyName Name -> NameAnnotation
registerBound = NameAction $ Changes DisappearsVariable

registerOutOfScope :: Either TyName Name -> NameAnnotation
registerOutOfScope = NameAction $ Persists StaysOutOfScopeVariable

registerFree :: Either TyName Name -> NameAnnotation
registerFree = NameAction $ Persists StaysFreeVariable

class EstablishScoping t where
    establishScoping :: t () -> t NameAnnotation

referenceInScopeTyName
    :: TyName -> Type TyName uni NameAnnotation -> Type TyName uni NameAnnotation
referenceInScopeTyName tyname = TyApp NotAName $ TyVar (registerBound $ Left tyname) tyname

referenceOutOfScopeTyName
    :: TyName -> Type TyName uni NameAnnotation -> Type TyName uni NameAnnotation
referenceOutOfScopeTyName tyname = TyApp NotAName $ TyVar (registerOutOfScope $ Left tyname) tyname

instance tyname ~ TyName => EstablishScoping (Type tyname uni) where
    establishScoping = go where
        go (TyLam _ name kind ty) =
            referenceOutOfScopeTyName name $
                TyLam (introduceBound $ Left name) name (NotAName <$ kind) $
                    referenceInScopeTyName name $
                        go ty
        go (TyForall _ name kind ty) =
            referenceOutOfScopeTyName name $
                TyForall (introduceBound $ Left name) name (NotAName <$ kind) $
                    referenceInScopeTyName name $
                        go ty
        go (TyIFix _ pat arg) = TyIFix NotAName (go pat) (go arg)
        go (TyApp _ fun arg) = TyApp NotAName (go fun) (go arg)
        go (TyFun _ dom cod) = TyFun NotAName (go dom) (go cod)
        go (TyVar _ name) = TyVar (registerFree $ Left name) name
        go (TyBuiltin _ fun) = TyBuiltin NotAName fun

typeId :: Type TyName uni ()
typeId = runQuote $ do
    x <- freshTyName "x"
    pure . TyLam () x (Type ()) $ TyVar () x

-- >>> :set -XTypeApplications
-- >>> collectScopeInfoType . runQuote . rename . establishScoping $ dissociateType @DefaultUni typeId
-- Right (ScopeInfo {unScopeInfo = fromList [(AppearedBindings,fromList [Left (TyName {unTyName = Name {nameString = "x", nameUnique = Unique {unUnique = 2}}})]),(AppearedVariables,fromList [Left (TyName {unTyName = Name {nameString = "x", nameUnique = Unique {unUnique = 2}}})]),(StayedOutOfScopeVariables,fromList [Left (TyName {unTyName = Name {nameString = "x", nameUnique = Unique {unUnique = 0}}})]),(StayedFreeVariables,fromList [Left (TyName {unTyName = Name {nameString = "x", nameUnique = Unique {unUnique = 1}}})])]})
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

data ScopeEntry
    = DisappearedBindings
    | DisappearedVariables
    | AppearedBindings
    | AppearedVariables
    | StayedOutOfScopeVariables
    | StayedFreeVariables
    deriving (Show, Eq, Ord)

newtype ScopeInfo = ScopeInfo
    { unScopeInfo :: Map ScopeEntry (Set (Either TyName Name))
    } deriving (Show)

data ScopeError = ScopeError Int
    deriving (Show)

toDisappearedBindings :: ScopeInfo -> Set (Either TyName Name)
toDisappearedBindings = fromMaybe Set.empty . Map.lookup DisappearedBindings . unScopeInfo

toAppearedBindings :: ScopeInfo -> Set (Either TyName Name)
toAppearedBindings = fromMaybe Set.empty . Map.lookup AppearedBindings . unScopeInfo

emptyScopeInfos :: ScopeInfo
emptyScopeInfos = ScopeInfo Map.empty

mergeScopeInfos :: ScopeInfo -> ScopeInfo -> Either ScopeError ScopeInfo
mergeScopeInfos si1 si2
    | toDisappearedBindings si1 `Set.intersection` toDisappearedBindings si2 /= Set.empty =
        Left $ ScopeError 1
    | toAppearedBindings si1 `Set.intersection` toAppearedBindings si2 /= Set.empty =
        Left $ ScopeError 2
    | otherwise = Right $ coerce (Map.unionWith Set.union) si1 si2

type NameMismatch = Either (TyName, TyName) (Name, Name)

overrideEName :: ScopeEntry -> Either TyName Name -> ScopeInfo -> ScopeInfo
overrideEName key = coerce . Map.insert key . Set.singleton

applyPersists :: Persists -> Either TyName Name -> ScopeInfo
applyPersists persists ename = overrideEName key ename emptyScopeInfos where
    key = case persists of
        StaysOutOfScopeVariable -> StayedOutOfScopeVariables
        StaysFreeVariable       -> StayedFreeVariables

applyChanges :: Changes -> Either TyName Name -> Either TyName Name -> ScopeInfo
applyChanges changes enameOld enameNew =
    overrideEName keyNew enameNew $ overrideEName keyOld enameOld emptyScopeInfos where
        (keyOld, keyNew) = case changes of
            DisappearsBinding  -> (AppearedBindings, AppearedBindings)
            DisappearsVariable -> (AppearedVariables, AppearedVariables)

-- data Changes
--     = DisappearsBinding
--     | DisappearsVariable
--     | AppearsBinding
--     | AppearsVariable
--     deriving (Show)


-- applyNameAction
--     :: Eq name
--     => (name -> Either TyName Name) -> NameAction -> name -> name -> Either ScopeError ScopeInfo
-- applyNameAction emb (Persists persists) enameOld enameNew =
--     if enameOld == enameNew then undefined else Left $ ScopeError 5
-- applyNameAction emb (Changes changes) enameOld enameNew =
--     if enameOld /= enameNew then undefined else Left $ ScopeError 6


applyNameAction
    :: NameAction -> Either TyName Name -> Either TyName Name -> Either ScopeError ScopeInfo
applyNameAction (Persists persists) enameOld enameNew =
    if enameOld == enameNew
        then Right $ applyPersists persists enameOld
        else Left $ ScopeError 5
applyNameAction (Changes changes) enameOld enameNew =
    if enameOld /= enameNew
        then Right $ applyChanges changes enameOld enameNew
        else Left $ ScopeError 6


handleName :: NameAnnotation -> Either TyName Name -> Either ScopeError ScopeInfo
handleName NotAName                      _       = Left $ ScopeError 3
handleName (NameAction action enameOld) enameNew =
    if isLeft enameOld == isLeft enameNew
        then applyNameAction action enameOld enameNew
        else Left $ ScopeError 4


-- data Persists
--     = StaysOutOfScopeVariable
--     | StaysFreeVariable
--     deriving (Show)

-- data Disappears
--     = DisappearsBinding
--     | DisappearsVariable
--     deriving (Show)

-- data Appears
--     = AppearsBinding
--     | AppearsVariable
--     deriving (Show)

-- data NameAction
--     = Persists Persists
--     | Disappears Disappears
--     | Appears Appears
--     deriving (Show)


-- We might want to use @Validation@ instead of 'Either'.
collectScopeInfoType :: Type TyName uni NameAnnotation -> Either ScopeError ScopeInfo
collectScopeInfoType = go where
    go (TyLam ann name _ ty)    = join $ mergeScopeInfos <$> handleName ann (Left name) <*> go ty
    go (TyForall ann name _ ty) = join $ mergeScopeInfos <$> handleName ann (Left name) <*> go ty
    go (TyIFix _ pat arg)       = join $ mergeScopeInfos <$> go pat <*> go arg
    go (TyApp _ fun arg)        = join $ mergeScopeInfos <$> go fun <*> go arg
    go (TyFun _ dom cod)        = join $ mergeScopeInfos <$> go dom <*> go cod
    go (TyVar ann name)         = handleName ann (Left name)
    go (TyBuiltin _ _ )         = Right emptyScopeInfos




-- DisappearedBindings  :: Set Unique \
--                                     -> Disappeared
-- DisappearedVars      :: Set Unique /

-- AppearedBindings     :: Set Unique \
--                                     -> Appeared
-- AppearedVars         :: Set Unique /

-- StayedOutOfScopeVars :: Set Unique  -- Do not have any relation to
-- StayedFreeVars       :: Set Unique


-- -- based on the assumption that at least one out-of-scope variable and at least one bound
-- -- variable get added for each binding
-- DisappearedBindings == DisappearedVars == StayedOutOfScopeVars
-- AppearedBindings == AppearedVars
-- DisappearedBindings `intersect` AppearedBindings == empty
-- DisappearedBindings `intersect` StayedFreeVars   == empty

-- size (DisappearedBindings `union` AppearedBindings `union` StayedFreeVars) ==
--   size DisappearedBindings + size AppearedBindings + size StayedFreeVars

-- stays => must be equal =>
















-- free variables
-- out of scope variables
-- disappeared bindings
-- disappeared variables



-- let y = (let x = a in b) in c
-- let y = (let x = a in b) in @out_of_scope x + c  -- ill-scoped


-- let nonrec @(add x_1 to notInScope, x_4 must not be in notInScope) x_4 = x_1 -> x_2 in x_4 -> x_3



-- data Scope name = Scope
--    { _inScope    :: Set name
--    , _notInScope :: Set name
--    }

-- data Scopes = Scopes
--     { _scopesType :: Scope TyName
--     , _scopesTerm :: Scope Name
--     }

-- emptyScope :: Scope name
-- emptyScope = Scope Set.empty Set.empty

-- emptyScopes :: Scopes
-- emptyScopes = Scopes emptyScope emptyScope

-- -- free stays
-- -- binding disappears
-- -- bound disappears
-- -- invisible added as free stays
-- data ScopeDelta
--     = StaysDelta (Either TyName Name)
--     | DisappearsDelta (Either TyName Name)
--     | NoChange
--     deriving (Show)

-- class Scoping t where
--     scoping :: t () -> t ScopeDelta

-- introduceBound :: Either TyName Name -> ScopeDelta
-- introduceBound = DisappearsDelta

-- -- registerBound :: Either TyName Name -> ScopeDelta
-- -- registerBound = NoChange

-- registerFree :: Either TyName Name -> ScopeDelta
-- registerFree = StaysDelta

-- -- referenceTyName :: TyName -> Type TyName uni ScopeDelta -> Type TyName uni ScopeDelta
-- -- referenceTyName tyname = TyFun NoChange $ TyVar (registerBound $ Left tyname) tyname

-- referenceTyName :: TyName -> Type TyName uni ScopeDelta -> Type TyName uni ScopeDelta
-- referenceTyName tyname = TyFun NoChange $ TyVar NoChange tyname

-- -- establishScoping
-- instance tyname ~ TyName => Scoping (Type tyname uni) where
--     scoping (TyLam _ name kind ty) =
--         TyLam (introduceBound $ Left name) name (NoChange <$ kind) $
--             referenceTyName name $ scoping ty
--     scoping (TyForall _ name kind ty) =
--         TyForall (introduceBound $ Left name) name (NoChange <$ kind) $
--             referenceTyName name $ scoping ty
--     scoping (TyIFix _ pat arg) = TyIFix NoChange (scoping pat) (scoping arg)
--     scoping (TyApp _ fun arg) = TyApp NoChange (scoping fun) (scoping arg)
--     scoping (TyFun _ dom cod) = TyFun NoChange (scoping dom) (scoping cod)
--     scoping (TyVar _ name) = TyVar (registerFree $ Left name) name
--     scoping (TyBuiltin _ fun) = TyBuiltin NoChange fun

-- -- 'deepOf' :: 'Traversal'' s s    -> 'Traversal'' s a             -> 'Traversal'' s a
-- -- deepOf :: 'Traversal' s t s t -> 'Traversal' s t a b          -> 'Traversal' s t a b

-- -- >>> :set -XTypeApplications
-- -- >>> runScopeM . checkScoping . runQuote . rename . scoping $ dissociateType @DefaultUni listTy
-- -- Right ()


-- -- >>> :set -XTypeApplications
-- -- >>> runQuote . rename . scoping $ dissociateType @DefaultUni listTy
-- -- TyLam (Disappears (Left (TyName {unTyName = Name {nameString = "a", nameUnique = Unique {unUnique = 0}}}))) (TyName {unTyName = Name {nameString = "a", nameUnique = Unique {unUnique = 11}}}) (Type NoChange) (TyIFix NoChange (TyLam (Disappears (Left (TyName {unTyName = Name {nameString = "list", nameUnique = Unique {unUnique = 1}}}))) (TyName {unTyName = Name {nameString = "list", nameUnique = Unique {unUnique = 12}}}) (KindArrow NoChange (Type NoChange) (Type NoChange)) (TyLam (Disappears (Left (TyName {unTyName = Name {nameString = "a", nameUnique = Unique {unUnique = 2}}}))) (TyName {unTyName = Name {nameString = "a", nameUnique = Unique {unUnique = 13}}}) (Type NoChange) (TyForall (Disappears (Left (TyName {unTyName = Name {nameString = "r", nameUnique = Unique {unUnique = 3}}}))) (TyName {unTyName = Name {nameString = "r", nameUnique = Unique {unUnique = 14}}}) (Type NoChange) (TyFun NoChange (TyVar (Disappears (Left (TyName {unTyName = Name {nameString = "r", nameUnique = Unique {unUnique = 3}}}))) (TyName {unTyName = Name {nameString = "r", nameUnique = Unique {unUnique = 14}}})) (TyFun NoChange (TyVar (Stays (Left (TyName {unTyName = Name {nameString = "r", nameUnique = Unique {unUnique = 4}}}))) (TyName {unTyName = Name {nameString = "r", nameUnique = Unique {unUnique = 4}}})) (TyFun NoChange (TyFun NoChange (TyVar (Stays (Left (TyName {unTyName = Name {nameString = "a", nameUnique = Unique {unUnique = 5}}}))) (TyName {unTyName = Name {nameString = "a", nameUnique = Unique {unUnique = 5}}})) (TyFun NoChange (TyApp NoChange (TyVar (Stays (Left (TyName {unTyName = Name {nameString = "list", nameUnique = Unique {unUnique = 6}}}))) (TyName {unTyName = Name {nameString = "list", nameUnique = Unique {unUnique = 6}}})) (TyVar (Stays (Left (TyName {unTyName = Name {nameString = "a", nameUnique = Unique {unUnique = 7}}}))) (TyName {unTyName = Name {nameString = "a", nameUnique = Unique {unUnique = 7}}}))) (TyVar (Stays (Left (TyName {unTyName = Name {nameString = "r", nameUnique = Unique {unUnique = 8}}}))) (TyName {unTyName = Name {nameString = "r", nameUnique = Unique {unUnique = 8}}})))) (TyVar (Stays (Left (TyName {unTyName = Name {nameString = "r", nameUnique = Unique {unUnique = 9}}}))) (TyName {unTyName = Name {nameString = "r", nameUnique = Unique {unUnique = 9}}})))))))) (TyVar (Stays (Left (TyName {unTyName = Name {nameString = "a", nameUnique = Unique {unUnique = 10}}}))) (TyName {unTyName = Name {nameString = "a", nameUnique = Unique {unUnique = 10}}})))
-- dissociateType :: Type TyName uni ann -> Type TyName uni ann
-- dissociateType = runQuote . go where
--     go (TyLam ann name kind ty) = do
--         nameFr <- freshenTyName name
--         TyLam ann nameFr kind <$> go ty
--     go (TyForall ann name kind ty) = do
--         nameFr <- freshenTyName name
--         TyForall ann nameFr kind <$> go ty
--     go (TyIFix ann pat arg) = TyIFix ann <$> go pat <*> go arg
--     go (TyApp ann fun arg) = TyApp ann <$> go fun <*> (go arg)
--     go (TyFun ann dom cod) = TyFun ann <$> go dom <*> go cod
--     go (TyVar ann name) = TyVar ann <$> freshenTyName name
--     go (TyBuiltin ann fun) = pure $ TyBuiltin ann fun

-- data ScopingError
--     = SupposedToBeInScope (Either TyName Name)
--     | NotSupposedToBeInScope (Either TyName Name)
--     | NotSupposedToBeNotInScope (Either TyName Name)
--     | FreeVariableRenamed (Either TyName Name)
--     deriving (Show)

-- type ScopeM = ReaderT Scopes (Either ScopingError)

-- runScopeM :: ScopeM a -> Either ScopingError a
-- runScopeM = flip runReaderT emptyScopes

-- class CheckScoping t where
--     checkScoping :: t ScopeDelta -> ScopeM ()

-- applyStays :: Ord name => name -> Scope name -> Scope name
-- applyStays name (Scope inScope notInScope) = Scope (Set.insert name inScope) notInScope

-- applyDisappears :: Ord name => name -> Scope name -> Scope name
-- applyDisappears name (Scope inScope notInScope) = Scope inScope (Set.insert name notInScope)

-- pickScopeAnd
--     :: (forall name. Ord name => name -> Scope name -> Scope name)
--     -> Either TyName Name
--     -> Scopes
--     -> Scopes
-- pickScopeAnd f (Left tyname) (Scopes typeScope termScope) = Scopes (f tyname typeScope) termScope
-- pickScopeAnd f (Right name)  (Scopes typeScope termScope) = Scopes typeScope (f name termScope)

-- applyScopeDelta :: ScopeDelta -> Scopes -> Scopes
-- applyScopeDelta (StaysDelta      ename) = pickScopeAnd applyStays      ename
-- applyScopeDelta (DisappearsDelta ename) = pickScopeAnd applyDisappears ename
-- applyScopeDelta NoChange                = id

-- withScopeDelta :: ScopeDelta -> ScopeM a -> ScopeM a
-- withScopeDelta = withReaderT . applyScopeDelta

-- -- if appears then in scope VS has to appear

-- -- bound => notInScope => can't appear
-- -- stays => free => annotation equals name

-- checkScopingName :: Ord name => (name -> Either TyName Name) -> name -> Scope name -> ScopeM ()
-- checkScopingName emb name (Scope inScope notInScope) = do
--     unless (name `Set.member` inScope) $ throwError . SupposedToBeInScope $ emb name
--     unless (name `Set.notMember` notInScope) $ throwError . NotSupposedToBeInScope $ emb name

-- checkScopingName' :: Ord name => (name -> Either TyName Name) -> name -> Scope name -> ScopeM ()
-- checkScopingName' emb name (Scope inScope notInScope) = do
--     unless (name `Set.notMember` inScope) $ throwError . NotSupposedToBeInScope $ emb name
--     unless (name `Set.notMember` notInScope) $ throwError . NotSupposedToBeNotInScope $ emb name

-- -- stays      => old equals new, sanity: old in old scope, old not notIn old scope
-- -- disappears => old not in old scope, new not in old scope, new not notIn old scope

-- -- \x_1 -> x_2
-- -- \@(disappears x_1) x_1 -> @(disappears x_1) x_1 -> @(stays x_2) x_2
-- -- \@(disappears x_1) x_3 -> @(disappears x_1) x_3 -> @(stays x_2) x_2

-- -- \@(add x_1 to notInScope, x_3 must not be anywhere) x_3 -> @(x_1 must not be in inScope, must be in notInScope, x_3 must not to be anywhere) x_3 -> @(annotation x_2 must be equal to the variable, must not be in inScope, must not be in notInScope) x_2

-- -- checkScoping:
-- -- \@(add x_1 to notInScope, x_3 must not be in notInScope) x_3 -> @(x_1 must be in notInScope, x_3 must not be in notInScope) x_3 -> @(annotation x_2 must be equal to the variable, x_2 must not be in notInScope) x_2

-- -- wrong:
-- -- \x_2 -> x_* -> x_2  -- bound renamed to free -- not caught!
-- -- \x_1 -> x_* -> x_3  -- free changed
-- -- \x_3 -> x_1 -> x_2  -- bound renamed at introduction site but not use site

-- -- let nonrec x_1 = {- x_1 not visible in -} x_2 in x_3

-- -- let nonrec x_1 = x_1 -> x_2 in x_1 -> x_3

-- -- let nonrec @(disappears_binding x_1) x_1 = @(stays_out_of_scope x_1) x_1 -> @(stays_free x_2) x_2 in @(disappears_bound x_1) x_1 -> @(stays_free x_3) x_3

-- -- let nonrec @(disappears_binding x_1) x_4 = @(stays_out_of_scope x_1) x_1 -> @(stays_free x_2) x_2 in @(disappears_bound x_1) x_4 -> @(stays_free x_3) x_3

-- -- definition vs usage

-- -- @(disappears_binding x_1) x_4: x_1 must not be equal to x_4, x_1 is added to d_notInScope, x_4 is added to d_inScope
-- -- @(stays_out_of_scope x_1) x_1: x_1 must be equal to x_1, x_1 is added to u_outOfScope
-- -- @(stays_free x_2) x_2: x_2 must be equal to x_2, x_2 is added to u_notInScope



-- checkScopingVar :: ScopeDelta -> Either TyName Name -> ScopeM ()
-- checkScopingVar NoChange ename = do
--     Scopes typeScope termScope <- ask
--     case ename of
--         Left tyname -> checkScopingName' Left  tyname typeScope
--         Right name  -> checkScopingName' Right name   termScope
-- checkScopingVar delta    ename = do
--     Scopes typeScope termScope <- ask
--     case ename of
--         Left tyname -> checkScopingName Left  tyname typeScope
--         Right name  -> checkScopingName Right name   termScope
--     case delta of
--         -- One free variable was renamed to another one.
--         StaysDelta ename'      -> unless (ename == ename') . throwError $ FreeVariableRenamed ename
--         -- This should be caught via checking the not-in-scope part, but whatever.
--         DisappearsDelta ename2 -> unless (ename /= ename2) $ error "Something horribly wrong has happened: a variable is verified not to be in scope, yet it somehow equals the original in-scope variable"
--         NoChange          -> pure ()

-- instance tyname ~ TyName => CheckScoping (Type tyname uni) where
--     checkScoping ty0 = withScopeDelta (typeAnn ty0) $ case ty0 of
--         TyLam _ _ _ ty    -> checkScoping ty
--         TyForall _ _ _ ty -> checkScoping ty
--         TyIFix _ pat arg  -> checkScoping pat *> checkScoping arg
--         TyApp _ fun arg   -> checkScoping fun *> checkScoping arg
--         TyFun _ dom cod   -> checkScoping dom *> checkScoping cod
--         TyVar delta name  -> checkScopingVar delta $ Left name
--         TyBuiltin _ _     -> pure ()
