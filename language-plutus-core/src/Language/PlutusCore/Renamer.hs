{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedStrings #-}

module Language.PlutusCore.Renamer ( rename
                                   , annotate
                                   , annotateST
                                   , NameWithType (..)
                                   , RenamedType
                                   , RenamedTerm
                                   , TyNameWithKind (..)
                                   , RenameError (..)
                                   , TypeState (..)
                                   ) where

import           Control.Monad.Except
import           Control.Monad.State.Lazy
import qualified Data.IntMap               as IM
import           Language.PlutusCore.Lexer
import           Language.PlutusCore.Name
import           Language.PlutusCore.Type
import           Lens.Micro
import           PlutusPrelude

data TypeState a = TypeState { _terms :: IM.IntMap (RenamedType a), _types :: IM.IntMap (Kind a) }

terms :: Lens' (TypeState a) (IM.IntMap (RenamedType a))
terms f s = fmap (\x -> s { _terms = x }) (f (_terms s))

types :: Lens' (TypeState a) (IM.IntMap (Kind a))
types f s = fmap (\x -> s { _types = x }) (f (_types s))

instance Semigroup (TypeState a) where
    (<>) (TypeState x x') (TypeState y y') = TypeState (x <> y) (x' <> y')

instance Monoid (TypeState a) where
    mempty = TypeState mempty mempty
    mappend = (<>)

type TypeM a = StateT (TypeState a) (Either (RenameError a))

type RenamedTerm a = Term TyNameWithKind NameWithType a
newtype NameWithType a = NameWithType (Name (a, RenamedType a))
    deriving (Functor, Pretty, Debug)
type RenamedType a = Type TyNameWithKind a
newtype TyNameWithKind a = TyNameWithKind { unTyNameWithKind :: TyName (a, Kind a) }
    deriving (Eq, Functor, Pretty, Debug)

-- | A 'RenameError' is thrown when a free variable is encountered during
-- rewriting.
data RenameError a = UnboundVar (Name a)
                   | UnboundTyVar (TyName a)

instance Pretty (RenameError AlexPosn) where
    pretty (UnboundVar n@(Name loc _ _)) = "Error at" <+> pretty loc <> ". Variable" <+> pretty n <+> "is not in scope."
    pretty (UnboundTyVar n@(TyName (Name loc _ _))) = "Error at" <+> pretty loc <> ". Type variable" <+> pretty n <+> "is not in scope."

instance Debug (RenameError AlexPosn) where
    debug (UnboundVar n@(Name loc _ _)) = "Error at" <+> pretty loc <> ". Variable" <+> debug n <+> "is not in scope."
    debug (UnboundTyVar n@(TyName (Name loc _ _))) = "Error at" <+> pretty loc <> ". Type variable" <+> debug n <+> "is not in scope."

-- | Annotate a program with type/kind information at all bound variables,
-- failing if we encounter a free variable.
annotate :: Program TyName Name a -> Either (RenameError a) (Program TyNameWithKind NameWithType a)
annotate = fmap snd . annotateST

-- | Annotate a program with type/kind information at all bound variables,
-- additionally returning a 'TypeState'
annotateST :: Program TyName Name a -> Either (RenameError a) (TypeState a, Program TyNameWithKind NameWithType a)
annotateST (Program x v p) = do
    (t, st) <- runStateT (annotateTerm p) mempty
    pure (st, Program x v t)

insertType :: Int -> Type TyNameWithKind a -> TypeM a ()
insertType = modify .* over terms .* IM.insert

insertKind :: Int -> Kind a -> TypeM a ()
insertKind = modify .* over types .* IM.insert

annotateTerm :: Term TyName Name a -> TypeM a (RenamedTerm a)
annotateTerm (Var x (Name x' b (Unique u))) = do
    st <- gets _terms
    case IM.lookup u st of
        Just ty -> pure $ Var x (NameWithType (Name (x', ty) b (Unique u)))
        Nothing -> throwError $ UnboundVar (Name x' b (Unique u))
annotateTerm (LamAbs x (Name x' s u@(Unique i)) ty t) = do
    aty <- annotateType ty
    let nwt = NameWithType (Name (x', aty) s u)
    insertType i aty
    LamAbs x nwt aty <$> annotateTerm t
annotateTerm (TyAbs x (TyName (Name x' b u@(Unique i))) k t) = do
    insertKind i k
    let nwty = TyNameWithKind (TyName (Name (x', k) b u))
    TyAbs x nwty k <$> annotateTerm t
annotateTerm (Unwrap x t) =
    Unwrap x <$> annotateTerm t
annotateTerm (Error x ty) =
    Error x <$> annotateType ty
annotateTerm (Apply x t t') =
    Apply x <$> annotateTerm t <*> annotateTerm t'
annotateTerm (Constant x c) =
    pure (Constant x c)
annotateTerm (TyInst x t ty) =
    TyInst x <$> annotateTerm t <*> annotateType ty
annotateTerm (Wrap x (TyName (Name x' b u@(Unique i))) ty t) = do
    aty <- annotateType ty
    let k = Type x'
    insertKind i k
    let nwty = TyNameWithKind (TyName (Name (x', k) b u))
    Wrap x nwty aty <$> annotateTerm t

annotateType :: Type TyName a -> TypeM a (RenamedType a)
annotateType (TyVar x (TyName (Name x' b (Unique u)))) = do
    st <- gets _types
    case IM.lookup u st of
        Just ty -> pure $ TyVar x (TyNameWithKind (TyName (Name (x', ty) b (Unique u))))
        Nothing -> throwError $ UnboundVar (Name x' b (Unique u))
annotateType (TyLam x (TyName (Name x' s u@(Unique i))) k ty) = do
    insertKind i k
    let nwty = TyNameWithKind (TyName (Name (x', k) s u))
    TyLam x nwty k <$> annotateType ty
annotateType (TyForall x (TyName (Name x' s u@(Unique i))) k ty) = do
    insertKind i k
    let nwty = TyNameWithKind (TyName (Name (x', k) s u))
    TyForall x nwty k <$> annotateType ty
annotateType (TyFix x (TyName (Name x' s u@(Unique i))) ty) = do
    let k = Type x'
    insertKind i k
    let nwty = TyNameWithKind (TyName (Name (x', k) s u))
    TyFix x nwty <$> annotateType ty
annotateType (TyFun x ty ty') =
    TyFun x <$> annotateType ty <*> annotateType ty'
annotateType (TyApp x ty ty') =
    TyApp x <$> annotateType ty <*> annotateType ty'
annotateType (TyBuiltin x tyb) = pure (TyBuiltin x tyb)
annotateType (TyInt x n) = pure (TyInt x n)

-- This renames terms so that they have a unique identifier. This is useful
-- because of scoping.
rename :: IdentifierState -> Program TyName Name a -> Program TyName Name a
rename (st, _, nextU) (Program x v p) = Program x v (evalState (renameTerm (Identifiers st') p) m)
    where st' = IM.fromList (zip keys keys)
          keys = IM.keys st
          -- the next unique is one more than the maximum
          m = unUnique nextU-1

newtype Identifiers = Identifiers { _identifiers :: IM.IntMap Int }

type MaxM = State Int

identifiers :: Lens' Identifiers (IM.IntMap Int)
identifiers f s = fmap (\x -> s { _identifiers = x }) (f (_identifiers s))

modifyIdentifiers :: Int -> Int -> Identifiers -> Identifiers
modifyIdentifiers u m = over identifiers (IM.insert u (m+1))

lookupId :: Int -> Identifiers -> Maybe Int
lookupId u st = IM.lookup u (_identifiers st)

-- this convoluted affair lets us track the maximum in a global state monad,
-- while keeping the table for renaming local (so that we don't rename things in
-- function applications)
renameTerm :: Identifiers -> Term TyName Name a -> MaxM (Term TyName Name a)
renameTerm st t@(LamAbs x (Name x' s (Unique u)) ty t') = do
    m <- get
    let st' = modifyIdentifiers u m st
        pastDef = lookupId u st
    case pastDef of
        Just _ ->
            modify (+1) >>
            LamAbs x (Name x' s (Unique (m+1))) <$> renameType st' ty <*> renameTerm st' t'
        _      -> renameTerm st' t
renameTerm st t@(Wrap x (TyName (Name x' s (Unique u))) ty t') = do
    m <- get
    let st' = modifyIdentifiers u m st
        pastDef = lookupId u st
    case pastDef of
        Just _ ->
            modify (+1) >>
            Wrap x (TyName (Name x' s (Unique (m+1)))) <$> renameType st' ty <*> renameTerm st' t'
        _ -> renameTerm st' t
renameTerm st t@(TyAbs x (TyName (Name x' s (Unique u))) k t') = do
    m <- get
    let st' = modifyIdentifiers u m st
        pastDef = lookupId u st
    case pastDef of
        Just _ ->
            modify (+1) >>
            TyAbs x (TyName (Name x' s (Unique (m+1)))) k <$> renameTerm st' t'
        _ -> renameTerm st' t
renameTerm st t@(Var x (Name x' s (Unique u))) =
    case pastDef of
        Just j -> pure $ Var x (Name x' s (Unique j))
        _      -> pure t
    where pastDef = lookupId u st
renameTerm st (Apply x t t') = Apply x <$> renameTerm st t <*> renameTerm st t'
renameTerm st (Unwrap x t) = Unwrap x <$> renameTerm st t
renameTerm _ x@Constant{} = pure x
renameTerm st (Error x ty) = Error x <$> renameType st ty
renameTerm st (TyInst x t tys) = TyInst x <$> renameTerm st t <*> renameType st tys

renameType :: Identifiers -> Type TyName a -> MaxM (Type TyName a)
renameType _ ty@TyInt{} = pure ty
renameType st ty@(TyLam x (TyName (Name x' s (Unique u))) k ty') = do
    m <- get
    let st' = modifyIdentifiers u m st
        pastDef = lookupId u st
    case pastDef of
        Just _ ->
            modify (+1) >>
            TyLam x (TyName (Name x' s (Unique (m+1)))) k <$> renameType st' ty'
        _ -> renameType st' ty
renameType st ty@(TyForall x (TyName (Name x' s (Unique u))) k ty') = do
    m <- get
    let st' = modifyIdentifiers u m st
        pastDef = lookupId u st
    case pastDef of
        Just _ ->
            modify (+1) >>
            TyForall x (TyName (Name x' s (Unique (m+1)))) k <$> renameType st' ty'
        _ -> renameType st' ty
renameType st ty@(TyFix x (TyName (Name x' s (Unique u))) ty') = do
    m <- get
    let st' = modifyIdentifiers u m st
        pastDef = lookupId u st
    case pastDef of
        Just _ ->
            modify (+1) >>
            TyFix x (TyName (Name x' s (Unique (m+1)))) <$> renameType st' ty'
        _ -> renameType st' ty
renameType st ty@(TyVar x (TyName (Name x' s (Unique u)))) =
    case pastDef of
        Just j -> pure $ TyVar x (TyName (Name x' s (Unique j)))
        _      -> pure ty
    where pastDef = lookupId u st
renameType st (TyApp x ty ty') = TyApp x <$> renameType st ty <*> renameType st ty'
renameType st (TyFun x ty ty') = TyFun x <$> renameType st ty <*> renameType st ty'
renameType _ ty@TyBuiltin{} = pure ty
