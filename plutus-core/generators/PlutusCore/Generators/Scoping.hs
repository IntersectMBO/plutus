{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE TypeFamilies          #-}

{-# LANGUAGE OverloadedStrings     #-}

module PlutusCore.Generators.Scoping where

import           PlutusCore
import           PlutusCore.Quote

import           Control.Monad.Except
import           Data.Coerce
import           Data.Either
import           Data.Map.Strict                  as Map
import           Data.Maybe
import           Data.Set                         as Set

import           PlutusCore.StdLib.Data.ScottList

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
-- @(stays_out_of_scope x_1) x_1 (\(@disappears_binding x_1) x_1 -> @(disappears_variable x_1) x_1 @(stays_free x_2) x_2)
-- @(stays_out_of_scope x_1) x_1 (\(@disappears_binding x_1) x_3 -> @(disappears_variable x_1) x_3 @(stays_free x_2) x_2)

data Persists
    = StaysOutOfScopeVariable
    | StaysFreeVariable
    deriving (Show)

data Changes
    = DisappearsBinding
    | DisappearsVariable
    deriving (Show)

data NameAction
    = Persists Persists
    | Changes Changes
    deriving (Show)

data NameAnn
    = NameAction NameAction (Either TyName Name)
    | NotAName
    deriving (Show)

class LiftToScope n where
    liftToScope :: n -> Either TyName Name

instance LiftToScope TyName where
    liftToScope = Left

instance LiftToScope Name where
    liftToScope = Right

introduceBound :: LiftToScope n => n -> NameAnn
introduceBound = NameAction (Changes DisappearsBinding) . liftToScope

registerBound :: LiftToScope n => n -> NameAnn
registerBound = NameAction (Changes DisappearsVariable) . liftToScope

registerOutOfScope :: LiftToScope n => n -> NameAnn
registerOutOfScope = NameAction (Persists StaysOutOfScopeVariable) . liftToScope

registerFree :: LiftToScope n => n -> NameAnn
registerFree = NameAction (Persists StaysFreeVariable) . liftToScope

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

to :: ScopeEntry -> ScopeInfo -> Set (Either TyName Name)
to entry = fromMaybe Set.empty . Map.lookup entry . unScopeInfo

emptyScopeInfo :: ScopeInfo
emptyScopeInfo = ScopeInfo Map.empty

mergeScopeInfo :: ScopeInfo -> ScopeInfo -> Either ScopeError ScopeInfo
mergeScopeInfo si1 si2
    | to DisappearedBindings si1 `Set.intersection` to DisappearedBindings si2 /= Set.empty =
        Left $ ScopeError 1
    | to AppearedBindings si1 `Set.intersection` to AppearedBindings si2 /= Set.empty =
        Left $ ScopeError 2
    | otherwise = Right $ coerce (Map.unionWith Set.union) si1 si2

overrideEName :: ScopeEntry -> Either TyName Name -> ScopeInfo -> ScopeInfo
overrideEName key = coerce . Map.insert key . Set.singleton

applyPersists :: Persists -> Either TyName Name -> ScopeInfo
applyPersists persists ename = overrideEName key ename emptyScopeInfo where
    key = case persists of
        StaysOutOfScopeVariable -> StayedOutOfScopeVariables
        StaysFreeVariable       -> StayedFreeVariables

applyChanges :: Changes -> Either TyName Name -> Either TyName Name -> ScopeInfo
applyChanges changes enameOld enameNew =
    overrideEName keyNew enameNew $ overrideEName keyOld enameOld emptyScopeInfo where
        (keyOld, keyNew) = case changes of
            DisappearsBinding  -> (DisappearedBindings, AppearedBindings)
            DisappearsVariable -> (DisappearedVariables, AppearedVariables)

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

handleName :: LiftToScope name => NameAnn -> name -> Either ScopeError ScopeInfo
handleName NotAName                     _       = Left $ ScopeError 3
handleName (NameAction action enameOld) nameNew = do
    let enameNew = liftToScope nameNew
    if isLeft enameOld == isLeft enameNew
        then applyNameAction action enameOld enameNew
        else Left $ ScopeError 4

checkScopeInfo :: ScopeInfo -> Either ScopeError ()
checkScopeInfo scopeInfo = do
    let disappearedBindings       = to DisappearedBindings       scopeInfo
        disappearedVariables      = to DisappearedVariables      scopeInfo
        appearedBindings          = to AppearedBindings          scopeInfo
        appearedVariables         = to AppearedVariables         scopeInfo
        stayedOutOfScopeVariables = to StayedOutOfScopeVariables scopeInfo
        stayedFreeVariables       = to StayedFreeVariables       scopeInfo
    -- The next three are based on the assumption that for each binder we add at least one
    -- out-of-scope variable and at least one in-scope one.
    unless (disappearedBindings == disappearedVariables) $
        Left $ ScopeError 10
    unless (disappearedBindings == stayedOutOfScopeVariables) $
        Left $ ScopeError 11
    unless (appearedBindings == appearedVariables) $
        Left $ ScopeError 12
    unless (disappearedBindings `Set.intersection` appearedBindings == Set.empty) $
        Left $ ScopeError 13
    unless (disappearedBindings `Set.intersection` stayedFreeVariables == Set.empty) $
        Left $ ScopeError 14
    unless (appearedBindings `Set.intersection` stayedFreeVariables == Set.empty) $
        Left $ ScopeError 15





class Scoping t where
    establishScoping :: MonadQuote m => t ann -> m (t NameAnn)

    -- We might want to use @Validation@ instead of 'Either'.
    collectScopeInfo :: t NameAnn -> Either ScopeError ScopeInfo

checkScopingUsingSpineOf :: (Scoping t, Rename (t NameAnn)) => t ann -> Either ScopeError ()
checkScopingUsingSpineOf =
    checkScopeInfo <=< collectScopeInfo . runQuote . rename . runQuote . establishScoping

class Reference n t where
    referenceVia
        :: (forall n. LiftToScope n => n -> NameAnn)
        -> n
        -> t NameAnn
        -> t NameAnn

referenceInScope :: Reference n t => n -> t NameAnn -> t NameAnn
referenceInScope = referenceVia registerBound

referenceOutOfScope :: Reference n t => n -> t NameAnn -> t NameAnn
referenceOutOfScope = referenceVia registerOutOfScope



instance tyname ~ TyName => Reference TyName (Type tyname uni) where
    referenceVia reg tyname ty = TyApp NotAName ty $ TyVar (reg tyname) tyname

instance tyname ~ TyName => Reference TyName (Term tyname name uni fun) where
    referenceVia reg tyname term = TyInst NotAName term $ TyVar (reg tyname) tyname

instance name ~ Name => Reference Name (Term tyname name uni fun) where
    referenceVia reg name term = Apply NotAName term $ Var (reg name) name

establishScopingBinder
    :: (Reference name lower, LiftToScope name, Scoping upper, Scoping lower, MonadQuote m)
    => (NameAnn -> name -> upper NameAnn -> lower NameAnn -> lower NameAnn)
    -> name
    -> upper ann
    -> lower ann
    -> m (lower NameAnn)
establishScopingBinder binder name upper lower = do
    upperS <- establishScoping upper
    referenceOutOfScope name .
        binder (introduceBound name) name upperS .
            referenceInScope name <$>
                establishScoping lower

instance Scoping Kind where
    establishScoping kind = pure $ NotAName <$ kind
    collectScopeInfo _ = Right emptyScopeInfo

instance tyname ~ TyName => Scoping (Type tyname uni) where
    establishScoping (TyLam _ nameDup kind ty) = do
        name <- freshenTyName nameDup
        establishScopingBinder TyLam name kind ty
    establishScoping (TyForall _ nameDup kind ty) = do
        name <- freshenTyName nameDup
        establishScopingBinder TyForall name kind ty
    establishScoping (TyIFix _ pat arg) =
        TyIFix NotAName <$> establishScoping pat <*> establishScoping arg
    establishScoping (TyApp _ fun arg) =
        TyApp NotAName <$> establishScoping fun <*> establishScoping arg
    establishScoping (TyFun _ dom cod) =
        TyFun NotAName <$> establishScoping dom <*> establishScoping cod
    establishScoping (TyVar _ nameDup) = do
        name <- freshenTyName nameDup
        pure $ TyVar (registerFree name) name
    establishScoping (TyBuiltin _ fun) = pure $ TyBuiltin NotAName fun

    collectScopeInfo (TyLam ann name _ ty) =
        join $ mergeScopeInfo <$> handleName ann name <*> collectScopeInfo ty
    collectScopeInfo (TyForall ann name _ ty) =
        join $ mergeScopeInfo <$> handleName ann name <*> collectScopeInfo ty
    collectScopeInfo (TyIFix _ pat arg) =
        join $ mergeScopeInfo <$> collectScopeInfo pat <*> collectScopeInfo arg
    collectScopeInfo (TyApp _ fun arg) =
        join $ mergeScopeInfo <$> collectScopeInfo fun <*> collectScopeInfo arg
    collectScopeInfo (TyFun _ dom cod) =
        join $ mergeScopeInfo <$> collectScopeInfo dom <*> collectScopeInfo cod
    collectScopeInfo (TyVar ann name) = handleName ann name
    collectScopeInfo (TyBuiltin _ _ ) = Right emptyScopeInfo

instance (tyname ~ TyName, name ~ Name) => Scoping (Term tyname name uni fun) where
    establishScoping (LamAbs _ nameDup ty body)  = do
        name <- freshenName nameDup
        establishScopingBinder LamAbs name ty body
    establishScoping (TyAbs _ nameDup kind body) = do
        name <- freshenTyName nameDup
        establishScopingBinder TyAbs name kind body
    establishScoping (IWrap _ pat arg term)   =
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

    -- collectScopeInfo (LamAbs _ name ty body)  = do
    --     join $ mergeScopeInfo <$> handleName ann name <*> collectScopeInfo ty
    -- collectScopeInfo (TyAbs _ nameDup kind body) = do
    --     name <- freshenTyName nameDup
    --     collectScopeInfoBinder TyAbs name kind body
    -- collectScopeInfo (IWrap _ pat arg term)   =
    --     IWrap NotAName <$> collectScopeInfo pat <*> collectScopeInfo arg <*> collectScopeInfo term
    -- collectScopeInfo (Apply _ fun arg) =
    --     Apply NotAName <$> collectScopeInfo fun <*> collectScopeInfo arg
    -- collectScopeInfo (Unwrap _ term) = Unwrap NotAName <$> collectScopeInfo term
    -- collectScopeInfo (Error _ ty) = Error NotAName <$> collectScopeInfo ty
    -- collectScopeInfo (TyInst _ term ty) =
    --     TyInst NotAName <$> collectScopeInfo term <*> collectScopeInfo ty
    -- collectScopeInfo (Var _ nameDup) = do
    --     name <- freshenName nameDup
    --     pure $ Var (registerFree name) name
    -- collectScopeInfo (Constant _ con) = pure $ Constant NotAName con
    -- collectScopeInfo (Builtin _ bi) = pure $ Builtin NotAName bi

-- instance tyname ~ TyName => Scoping (Type tyname uni) where
--     establishScoping = runQuote . go where
--         go (TyLam _ nameDup kind ty) = do
--             name <- freshenTyName nameDup
--             referenceOutOfScopeTyName name .
--                 TyLam (introduceBound $ Left name) name (NotAName <$ kind) .
--                     referenceInScopeTyName name <$>
--                         go ty
--         go (TyForall _ nameDup kind ty) = do
--             name <- freshenTyName nameDup
--             referenceOutOfScopeTyName name .
--                 TyForall (introduceBound $ Left name) name (NotAName <$ kind) .
--                     referenceInScopeTyName name <$>
--                         go ty
--         go (TyIFix _ pat arg) = TyIFix NotAName <$> go pat <*> go arg
--         go (TyApp _ fun arg) = TyApp NotAName <$> go fun <*> go arg
--         go (TyFun _ dom cod) = TyFun NotAName <$> go dom <*> go cod
--         go (TyVar _ nameDup) = do
--             name <- freshenTyName nameDup
--             pure $ TyVar (registerFree $ Left name) name
--         go (TyBuiltin _ fun) = pure $ TyBuiltin NotAName fun

typeId :: Type TyName uni ()
typeId = runQuote $ do
    x <- freshTyName "x"
    pure . TyLam () x (Type ()) $ TyVar () x

-- >>> :set -XTypeApplications
-- >>> checkScopingUsingSpineOf $ listTy @DefaultUni
-- Right ()
