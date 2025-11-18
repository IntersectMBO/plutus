{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}

module PlutusIR.Pass where

import PlutusIR.Check.Uniques qualified as Uniques
import PlutusIR.Core.Type
import PlutusIR.Error
import PlutusIR.TypeCheck qualified as TC

import PlutusCore qualified as PLC
import PlutusCore.Builtin (AnnotateCaseBuiltin)
import PlutusCore.Name.Unique

import Control.Monad (void, when)
import Control.Monad.Except
import Control.Monad.Trans.Class (lift)
import Data.Foldable
import Data.Text (Text)
import PlutusCore.Quote

-- | A condition on a 'Term'.
data Condition tyname name uni fun a where
  -- | The 'Term' typechecks.
  Typechecks
    :: (PLC.Typecheckable uni fun, PLC.GEq uni)
    => TC.PirTCConfig uni fun -> Condition TyName Name uni fun a
  -- | The 'Term' has globally unique names.
  GloballyUniqueNames
    :: (HasUnique tyname TypeUnique, HasUnique name TermUnique, Ord a)
    => Condition tyname name uni fun a
  {-| A custom condition. 'Nothing' indicates success, 'Just' indicates a failure at
  a location with a message. -}
  Custom
    :: (Term tyname name uni fun a -> Maybe (a, Text))
    -> Condition tyname name uni fun a

-- | A condition on a pair of 'Term's.
data BiCondition tyname name uni fun a where
  -- | A condition on the second 'Term'.
  ConstCondition :: Condition tyname name uni fun a -> BiCondition tyname name uni fun a
  {-| A custom condition. 'Nothing' indicates success, 'Just' indicates a failure at
  a location with a message. -}
  CustomBi
    :: (Term tyname name uni fun a -> Term tyname name uni fun a -> Maybe (a, Text))
    -> BiCondition tyname name uni fun a

checkCondition
  :: (MonadError (Error uni fun a) m, AnnotateCaseBuiltin uni)
  => Condition tyname name uni fun a
  -> Term tyname name uni fun a
  -> m ()
checkCondition c t = case c of
  Typechecks tcconfig -> void $ runQuoteT $ do
    -- Typechecking requires globally unique names
    renamed <- PLC.rename t
    TC.inferType tcconfig renamed
  GloballyUniqueNames ->
    void $
      modifyError (PLCError . PLC.UniqueCoherencyErrorE) $
        Uniques.checkTerm (const True) t
  Custom f -> case f t of
    Just (a, e) -> throwError $ CompilationError a e
    Nothing -> pure ()

checkBiCondition
  :: (MonadError (Error uni fun a) m, AnnotateCaseBuiltin uni)
  => BiCondition tyname name uni fun a
  -> Term tyname name uni fun a
  -> Term tyname name uni fun a
  -> m ()
checkBiCondition c t1 t2 = case c of
  ConstCondition c' -> checkCondition c' t2
  CustomBi f -> case f t1 t2 of
    Just (a, e) -> throwError $ CompilationError a e
    Nothing -> pure ()

-- | A pass over a term, with pre- and post-conditions.
data Pass m tyname name uni fun a
  = {-| A basic pass. Has a function, which is the pass itself, a set of pre-conditions
    which are run on the input term, and a set of post-conditions which are run on the
    input and output terms (so can compare them). -}
    Pass
      (Term tyname name uni fun a -> m (Term tyname name uni fun a))
      [Condition tyname name uni fun a]
      [BiCondition tyname name uni fun a]
  | CompoundPass (Pass m tyname name uni fun a) (Pass m tyname name uni fun a)
  | NoOpPass
  | NamedPass String (Pass m tyname name uni fun a)

instance Semigroup (Pass m tyname name uni fun a) where
  p1 <> p2 = CompoundPass p1 p2

instance Monoid (Pass m tyname name uni fun a) where
  mempty = NoOpPass

hoistPass :: (forall v. m v -> n v) -> Pass m tyname name uni fun a -> Pass n tyname name uni fun a
hoistPass f p = case p of
  Pass mainPass pre post -> Pass (f . mainPass) pre post
  CompoundPass p1 p2 -> CompoundPass (hoistPass f p1) (hoistPass f p2)
  NamedPass n pass -> NamedPass n (hoistPass f pass)
  NoOpPass -> NoOpPass

runPass
  :: (Monad m, AnnotateCaseBuiltin uni)
  => (String -> m ())
  -> Bool
  -> Pass m tyname name uni fun a
  -> Term tyname name uni fun a
  -> ExceptT (Error uni fun a) m (Term tyname name uni fun a)
runPass logger checkConditions (Pass mainPass pre post) t = do
  when checkConditions $ do
    lift $ logger "checking preconditions"
    for_ pre $ \c -> checkCondition c t
  t' <- lift $ mainPass t
  when checkConditions $ do
    lift $ logger "checking postconditions"
    for_ post $ \c -> checkBiCondition c t t'
  pure t'
runPass logger checkConditions (CompoundPass p1 p2) t = do
  t' <- runPass logger checkConditions p1 t
  runPass logger checkConditions p2 t'
runPass logger checkConditions (NamedPass n pass) t = do
  lift $ logger $ n ++ ": running pass"
  t' <- runPass logger checkConditions pass t
  lift $ logger $ n ++ ": finished pass"
  pure t'
runPass _ _ NoOpPass t = pure t

-- | A simple, non-monadic pass that should typecheck.
simplePass
  :: (PLC.Typecheckable uni fun, PLC.GEq uni, Applicative m)
  => String
  -> TC.PirTCConfig uni fun
  -> (Term TyName Name uni fun a -> Term TyName Name uni fun a)
  -> Pass m TyName Name uni fun a
simplePass name tcConfig f =
  NamedPass name $
    Pass (pure . f) [Typechecks tcConfig] [ConstCondition (Typechecks tcConfig)]

-- | A pass that does renaming.
renamePass
  :: (HasUnique name TermUnique, HasUnique tyname TypeUnique, MonadQuote m, Ord a)
  => Pass m tyname name uni fun a
renamePass =
  NamedPass "renaming" $
    Pass PLC.rename [] [ConstCondition GloballyUniqueNames]

{-| A pass that does typechecking, useful when you want to do it explicitly
and not as part of a precondition check. -}
typecheckPass
  :: (TC.MonadTypeCheckPir uni fun a m, Ord a)
  => TC.PirTCConfig uni fun
  -> Pass m TyName Name uni fun a
typecheckPass tcconfig = NamedPass "typechecking" $ Pass run [GloballyUniqueNames] []
  where
    run t = do
      _ <- TC.inferType tcconfig t
      pure t
