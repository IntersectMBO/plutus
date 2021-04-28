{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE LambdaCase           #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE UndecidableInstances #-}

{-# OPTIONS_GHC -fno-warn-orphans #-}

-- | Renaming of PIR terms. Import this module to bring the @PLC.Rename (Term tyname name uni fun ann)@
-- instance in scope.
module PlutusIR.Transform.Rename () where

import           PlutusIR

import qualified PlutusCore                 as PLC
import qualified PlutusCore.Name            as PLC
import qualified PlutusCore.Rename.Internal as PLC

import           Control.Monad.Reader
import           Control.Monad.Trans.Cont   (ContT (..))

import           Data.List.NonEmpty         (NonEmpty)

{- Note [Renaming of mutually recursive bindings]
The 'RenameM' monad is a newtype wrapper around @ReaderT renaming Quote@, so in order to bring
a name into the scope we need to use the following pattern:

    withFreshenedX :: X -> (X -> RenameM renaming c) -> RenameM renaming c

where an 'X' is some value that has names inside and the second argument is a continuation that
expects to receive this value, but with all the names freshened and with the mappings from the
old uniques to the new ones saved. For the latter reason we can't just write

    freshenX :: X -> RenameM renaming X

because if you write

    freshenX x >>= \xFr -> ...

then the mappings from the uniques of 'x' to the uniques of 'xFr' do not exist in @...@.

Two problems arise:

1. If you have a list of @X@s and then an @Y@ and then another list of @Z@s and you need to freshen
   all of those, it's not nice to compose @withFreshened*@ functions at all. In order to make these
   functions composable, we can wrap them in the 'ContT' monad. See e.g. 'renameDatatypeCM' below.
2. Handling of mutually recursive bindings requires to bring a bunch of bindings in scope first and
   only then to rename their RHSs. I.e. one part of a 'ScopedRenameM' computation must be performed
   immediately (brinding names in scope) and the other part must be postponed until all bindings
   are in scope (renaming of RHSs). We will refer to this scheme as "two-stage renaming".

   Hence we have the following pattern:

       renameXCM :: X -> ContT c PLC.ScopedRenameM (PLC.ScopedRenameM X)

   where an 'X' is some value that defines some names and has types/terms that need to be renamed.
   The first 'PLC.ScopedRenameM' is for bringing names (the first stage) in scope and the second
   'PLC.ScopedRenameM' is for performing the renaming (the second stage).
-}

instance PLC.HasUniques (Term tyname name uni fun ann) => PLC.Rename (Term tyname name uni fun ann) where
    -- TODO: the Plutus Core codebase uses marking in order to prevent clashing with existing
    -- free variables. Should we do the same here?
    rename = PLC.runRenameT . renameTermM

-- See Note [Renaming of mutually recursive bindings].
-- | Rename a 'Datatype' in the CPS-transformed 'ScopedRenameM' monad.
renameDatatypeCM
    :: (PLC.HasUniques (Term tyname name uni fun ann), PLC.MonadQuote m)
    => Datatype tyname name uni fun ann
    -> ContT c (PLC.ScopedRenameT m) (PLC.ScopedRenameT m (Datatype tyname name uni fun ann))
renameDatatypeCM (Datatype x dataDecl params matchName constrs) = do
    -- The first stage (the data type itself, its constructors and its matcher get renamed).
    dataDeclFr  <- ContT $ PLC.withFreshenedTyVarDecl dataDecl
    constrsRen  <- traverse (ContT . PLC.withFreshenedVarDecl) constrs
    matchNameFr <- ContT $ PLC.withFreshenedName matchName
    -- The second stage (the type parameters and types of constructors get renamed).
    pure $
        runContT (traverse (ContT . PLC.withFreshenedTyVarDecl) params) $ \paramsFr ->
            Datatype x dataDeclFr paramsFr matchNameFr <$> sequence constrsRen

-- | Rename a 'Binding' in the CPS-transformed 'ScopedRenameM' monad.
renameBindingCM
    :: (PLC.HasUniques (Term tyname name uni fun ann), PLC.MonadQuote m)
    => Binding tyname name uni fun ann
    -> ContT c (PLC.ScopedRenameT m) (PLC.ScopedRenameT m (Binding tyname name uni fun ann))
renameBindingCM = \case
    TermBind x s var term -> do
        -- The first stage (the variable gets renamed).
        varRen <- ContT $ PLC.withFreshenedVarDecl var
        -- The second stage (the type of the variable and the RHS get renamed).
        pure $ TermBind x s <$> varRen <*> renameTermM term
    TypeBind x var ty -> do
        -- The first stage (the variable gets renamed).
        varFr <- ContT $ PLC.withFreshenedTyVarDecl var
        -- The second stage (the RHS gets renamed).
        pure $ TypeBind x varFr <$> PLC.renameTypeM ty
    DatatypeBind x datatype ->
        -- Both the stages of 'renameDatatypeCM'.
        fmap (DatatypeBind x) <$> renameDatatypeCM datatype

-- | Replace the uniques in the names stored in a bunch of bindings by new uniques,
-- save the mapping from the old uniques to the new ones, rename the RHSs and
-- supply the updated bindings to a continuation.
withFreshenedBindings
    :: (PLC.HasUniques (Term tyname name uni fun ann), PLC.MonadQuote m)
    => Recursivity
    -> NonEmpty (Binding tyname name uni fun ann)
    -> (NonEmpty (Binding tyname name uni fun ann) -> PLC.ScopedRenameT m c)
    -> PLC.ScopedRenameT m c
withFreshenedBindings recy binds cont = case recy of
    -- Bring each binding in scope, rename its RHS straight away, collect all the results and
    -- supply them to the continuation.
    NonRec -> runContT (traverse (renameBindingCM >=> lift) binds) cont
    -- First bring all bindinds in scope and only then rename their RHSs and
    -- supply the results to the continuation.
    Rec    -> runContT (traverse renameBindingCM binds) $ sequence >=> cont

-- | Rename a 'Term' in the 'ScopedRenameM' monad.
renameTermM
    :: (PLC.HasUniques (Term tyname name uni fun ann), PLC.MonadQuote m)
    => Term tyname name uni fun ann -> PLC.ScopedRenameT m (Term tyname name uni fun ann)
renameTermM = \case
    Let x r binds term ->
        withFreshenedBindings r binds $ \bindsFr ->
            Let x r bindsFr <$> renameTermM term
    Var x name ->
        Var x <$> PLC.renameNameM name
    TyAbs x name kind body ->
        PLC.withFreshenedName name $ \nameFr ->
            TyAbs x nameFr kind <$> renameTermM body
    LamAbs x name ty body ->
        PLC.withFreshenedName name $ \nameFr ->
            LamAbs x nameFr <$> PLC.renameTypeM ty <*> renameTermM body
    Apply x fun arg ->
        Apply x <$> renameTermM fun <*> renameTermM arg
    Constant x con ->
        pure $ Constant x con
    Builtin x bi ->
        pure $ Builtin x bi
    TyInst x term ty ->
        TyInst x <$> renameTermM term <*> PLC.renameTypeM ty
    Error x ty ->
        Error x <$> PLC.renameTypeM ty
    IWrap x pat arg term ->
        IWrap x <$> PLC.renameTypeM pat <*> PLC.renameTypeM arg <*> renameTermM term
    Unwrap x term ->
        Unwrap x <$> renameTermM term
