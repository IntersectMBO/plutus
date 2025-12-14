-- editorconfig-checker-disable-file
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

{-| Renaming of PIR terms. Import this module to bring the @PLC.Rename (Term tyname name uni fun ann)@
instance in scope. -}
module PlutusIR.Transform.Rename
  ( renameTermM
  , renameProgramM
  ) where

import PlutusPrelude

import PlutusIR
import PlutusIR.Mark

import PlutusCore qualified as PLC
import PlutusCore.Name.Unique qualified as PLC
import PlutusCore.Rename.Internal qualified as PLC

import Control.Monad.Reader
import Control.Monad.Trans.Cont (ContT (..))

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

{- Note [Weird IR data types]
We don't attempt to recognize in the renamer a family of mutually recursive data types where two
or more data types have the same name, so the renamer's behavior in that case is undefined.
The same applies to a data type having identically named constructors or when a constructor has
the same name as the matcher etc.

The AST of Plutus IR allows us to represent some weird data types like

    data D where
        C : integer -> (\d -> d) D

    data D where
        C : (\d -> d) (integer -> D)

We don't pretend that we can handle those at all. The renamer calls 'error' upon seeing anything of
this kind.

However this one:

    data D x where
        C : all D. D x -> D x

is perfectly unambiguous:

1. the head (@D@) of the application (@D x@) in the type of the result (after @->@) has to refer to
   the data type being defined and so @all D@ is not supposed to result in shadowing there
2. @all D@ shadows the name of the data type everywhere before the final @->@, so it does not matter
   whether @D@ is recursive or not as any @D@ before the final @->@ refers to the @all@-bound @D@
   regardless of recursivity.

Note that @all D@ is existential quantification and the type checker wasn't able to handle that at
the time this note was written.

Similarly, in

    data D D where
        C : D -> D

the parameter shadows the data type before @->@ and does not shadow it afterwards regardless of
recursivity.

Note also that for example the following:

    data D1 x where
        C1 : all x. D1 x

is not existential quantification and should mean the same thing as

    data D2 x where
        C2 : D2 x

but also was blowing up the type checker at the time the note was written.

Haskell agrees that these two data types are isomorphic:

    data D1 x where
        C1 :: forall x. D1 x

    data D2 x where
        C2 :: D2 x

    d12 :: D1 x -> D2 x
    d12 C1 = C2

    d21 :: D2 x -> D1 x
    d21 C2 = C1

Note @D1@ only requires @GADTSyntax@ and not full-blown @GADTs@.

Speaking of GADTs, the following data type:

    data D D where
        C : D D

is only unambiguous if we stipulate that GADTs are not allowed in Plutus IR (otherwise the last
@D@ could be an index referring to the data type rather than the parameter).

So what we do in the renamer is rename everything as normal apart from the head of the application
after the final @->@ in the type of a constructor (let's call that "the final head"). Instead, the
final head is renamed in the context that the whole data type is renamed in plus the name of the
data type, which ensures that neither parameters nor @all@-bound variables in the type of the
constructor can shadow the name of the data type in the final head. This effectively bans the
GADT interpretation of the @data D D@ example from the above thus removing ambiguity.

This agrees perfectly with what we need to do to handle recursivity in constructors, see
Note [Renaming of constructors].
-}

{- Note [Renaming of constructors]
Consider the following data type:

    data Loop where
        MkLoop : Loop -> Loop

Whether the occurrence of @Loop@ before @->@ in the type of @MkLoop@ refers to @Loop@-the-data-type
or not depends on whether the data type is declared as recursive or not. However the occurrence of
@Loop@ after @->@ always refers to @Loop@-the-data-type. So we can't just directly rename the type
of a constructor with some general 'renameTypeM' stuff, we have to actually traverse the type and
rename things before the final @->@ differently depending on recursivity without doing so for the
final type as was discussed in Note [Weird IR data types].

However the current context is stored inside the 'RenameT' transformer and changing it manually
would be quite unpleasant as 'RenameT' is designed specifically to abstract these details out.
Instead, we provide a function that captures the current context in a 'Restorer' that allows us
to restore that context later. We use the capturing function twice: right before binding the name
of a data type and right after, which gives us two respective restorers. The former restorer is
used when type checking constructors of non-recursive data types: binding the name of data type
ensures that the data type is visible after the 'DatatypeBind' entry of the corresponding @let@
and using the restorer ensures that the name of the data type is not visible in the type of
constructors (as the data type is non-recursive) apart from the final head. And since recursivity
has no impact on how the final head is renamed, we use the right-after-the-name-of-the-data-type
restorer once we reach the final head. This gives us a single function for renaming types of
constructors in both the recursive and non-recursive cases letting us handle recursivity with a
single line in the function renaming a data type.
-}

{- Note [Mutual vs non-mutual recursion]
Note [Renaming of mutually recursive bindings] describes how we handle recursive bindings.
There's nothing special about the way we handle non-recursive ones, however it's worth saying
explicitly that in

    let nonrec x = <...>

@x@ is not visible in @<...>@, which makes it hard to share code between functions that handle
recursive and non-recursive bindings, so we don't.

Note [Renaming of constructors] describes how we managed to handle types of constructors of
recursive and non-recursive data types with a single function.
-}

instance PLC.HasUniques (Term tyname name uni fun ann) => PLC.Rename (Term tyname name uni fun ann) where
  -- See Note [Marking]
  rename = through markNonFreshTerm >=> PLC.runRenameT . renameTermM

instance PLC.HasUniques (Term tyname name uni fun ann) => PLC.Rename (Program tyname name uni fun ann) where
  rename (Program ann v term) = Program ann v <$> PLC.rename term

-- See Note [Renaming of constructors].
-- | A wrapper around a function restoring some old context of the renamer.
newtype Restorer m = Restorer
  { unRestorer :: forall a. m a -> m a
  }

-- | Capture the current context in a 'Restorer'.
captureContext :: MonadReader ren m => ContT c m (Restorer m)
captureContext = ContT $ \k -> do
  env <- ask
  k $ Restorer $ local $ const env

type MonadRename m = (PLC.MonadQuote m, MonadReader PLC.ScopedRenaming m)

{-| Rename the type of a constructor given a restorer dropping all variables bound after the
name of the data type. -}
renameConstrTypeM
  :: (MonadRename m, PLC.HasUniques (Type tyname uni ann))
  => Restorer m -> Type tyname uni ann -> m (Type tyname uni ann)
renameConstrTypeM (Restorer restoreAfterData) = renameSpineM
  where
    renameSpineM (TyForall ann name kind ty) =
      PLC.withFreshenedName name $ \nameFr -> TyForall ann nameFr kind <$> renameSpineM ty
    renameSpineM (TyFun ann dom cod) = TyFun ann <$> PLC.renameTypeM dom <*> renameSpineM cod
    renameSpineM ty = renameResultM ty

    renameResultM (TyApp ann fun arg) = TyApp ann <$> renameResultM fun <*> PLC.renameTypeM arg
    renameResultM (TyVar ann name) = TyVar ann <$> restoreAfterData (PLC.renameNameM name)
    renameResultM _ =
      error "Panic: a constructor returns something that is not an iterated application of a type variable"

{-| Rename the name of a constructor immediately and defer renaming of its type until the second
stage where all mutually recursive data types (if any) are bound. -}
renameConstrCM
  :: (MonadRename m, PLC.HasUniques (Term tyname name uni fun ann))
  => Restorer m
  -> VarDecl tyname name uni ann
  -> ContT c m (m (VarDecl tyname name uni ann))
renameConstrCM restorerAfterData (VarDecl ann name ty) = do
  nameFr <- ContT $ PLC.withFreshenedName name
  pure $ VarDecl ann nameFr <$> renameConstrTypeM restorerAfterData ty

-- | Apply a function to a value in the non-recursive case and return the value unchanged otherwise.
onNonRec :: Recursivity -> (a -> a) -> a -> a
onNonRec NonRec f x = f x
onNonRec Rec _ x = x

-- See Note [Weird IR data types]
-- See Note [Renaming of constructors] (and make sure you understand all the intricacies in it
-- before toucing this function).
-- | Rename a 'Datatype' in the CPS-transformed 'ScopedRenameM' monad.
renameDatatypeCM
  :: (MonadRename m, PLC.HasUniques (Term tyname name uni fun ann))
  => Recursivity
  -> Datatype tyname name uni ann
  -> ContT c m (m (Datatype tyname name uni ann))
renameDatatypeCM recy (Datatype x dataDecl params matchName constrs) = do
  -- The first stage (the data type itself, its constructors and its matcher get renamed).
  -- Note that all of these are visible downstream.
  restorerBeforeData <- captureContext
  dataDeclFr <- ContT $ PLC.withFreshenedTyVarDecl dataDecl
  restorerAfterData <- captureContext
  constrsRen <- traverse (renameConstrCM restorerAfterData) constrs
  matchNameFr <- ContT $ PLC.withFreshenedName matchName
  -- The second stage (the type parameters and types of constructors get renamed).
  -- Note that parameters are only visible in the types of constructors and not downstream.
  pure . onNonRec recy (unRestorer restorerBeforeData) $
    runContT (traverse (ContT . PLC.withFreshenedTyVarDecl) params) $ \paramsFr ->
      Datatype x dataDeclFr paramsFr matchNameFr <$> sequence constrsRen

-- | Rename a 'Binding' from a non-recursive family in the CPS-transformed 'ScopedRenameM' monad.
renameBindingNonRecC
  :: (MonadRename m, PLC.HasUniques (Term tyname name uni fun ann))
  => Binding tyname name uni fun ann
  -> ContT c m (Binding tyname name uni fun ann)
-- Unlike in the recursive case we don't have any stage separation here.
--
-- 'TypeBind' is the simplest case: the body of the binding gets renamed first, then the name of
-- the binding is brought in scope (not the other way around! As that would bring the name of the
-- binding in scope in its own body, which is very wrong in the non-recursive case) and the
-- renamed 'TypeBind' is passed to the continuation.
--
-- 'TermBind' also requires us to discharge the computation returning a variable with a renamed term-- before feeding the continuation. The reason why 'withFreshenedVarDecl' provides the caller with a
-- computation rather than a pure term is because that is how we bring mutually recursive bindings
-- in scope first without renaming their types right away (as those can reference type bindings from
-- the same family) while still being able to perform the renaming later. But we don't need that
-- stage separation in the non-recursive case, hence the type of the binding is renamed right away.
--
-- 'DatatypeBind' is handled the same way as 'TermBind' except all the work is performed in
-- 'renameDatatypeCM' and here we just unwrap from 'ContT' and perform all the renaming saved for
-- stage two immediately just like in the 'TermBind' case and for the same reason.
renameBindingNonRecC binding = ContT $ \cont -> case binding of
  TermBind x s var term -> do
    termFr <- renameTermM term
    PLC.withFreshenedVarDecl var $ \varRen -> do
      varFr <- varRen
      cont $ TermBind x s varFr termFr
  TypeBind x var ty -> do
    tyFr <- PLC.renameTypeM ty
    PLC.withFreshenedTyVarDecl var $ \varFr ->
      cont $ TypeBind x varFr tyFr
  DatatypeBind x datatype -> do
    runContT (renameDatatypeCM NonRec datatype) $ \datatypeRen ->
      datatypeRen >>= cont . DatatypeBind x

-- | Rename a 'Binding' from a recursive family in the CPS-transformed 'ScopedRenameM' monad.
renameBindingRecCM
  :: (MonadRename m, PLC.HasUniques (Term tyname name uni fun ann))
  => Binding tyname name uni fun ann
  -> ContT c m (m (Binding tyname name uni fun ann))
renameBindingRecCM = \case
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
  DatatypeBind x datatype -> do
    -- The first stage.
    datatypeRen <- renameDatatypeCM Rec datatype
    -- The second stage.
    pure $ DatatypeBind x <$> datatypeRen

{-| Replace the uniques in the names stored in a bunch of bindings by new uniques,
save the mapping from the old uniques to the new ones, rename the RHSs and
supply the updated bindings to a continuation. -}
withFreshenedBindings
  :: (MonadRename m, PLC.HasUniques (Term tyname name uni fun ann))
  => Recursivity
  -> NonEmpty (Binding tyname name uni fun ann)
  -> (NonEmpty (Binding tyname name uni fun ann) -> m c)
  -> m c
withFreshenedBindings recy binds cont = case recy of
  -- Bring each binding in scope, rename its RHS straight away, collect all the results and
  -- supply them to the continuation.
  NonRec -> runContT (traverse renameBindingNonRecC binds) cont
  -- First bring all bindinds in scope and only then rename their RHSs and
  -- supply the results to the continuation.
  Rec -> runContT (traverse renameBindingRecCM binds) $ sequence >=> cont

-- | Rename a 'Term' in the 'ScopedRenameM' monad.
renameTermM
  :: (MonadRename m, PLC.HasUniques (Term tyname name uni fun ann))
  => Term tyname name uni fun ann -> m (Term tyname name uni fun ann)
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
  Constr x ty i es -> Constr x <$> PLC.renameTypeM ty <*> pure i <*> traverse renameTermM es
  Case x ty arg cs -> Case x <$> PLC.renameTypeM ty <*> renameTermM arg <*> traverse renameTermM cs

-- | Rename a 'Term' in the 'ScopedRenameM' monad.
renameProgramM
  :: (MonadRename m, PLC.HasUniques (Term tyname name uni fun ann))
  => Program tyname name uni fun ann -> m (Program tyname name uni fun ann)
renameProgramM (Program ann v term) = Program ann v <$> renameTermM term
