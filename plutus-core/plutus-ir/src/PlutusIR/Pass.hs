-- editorconfig-checker-disable-file
{-# LANGUAGE GADTs      #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes #-}

module PlutusIR.Pass where

import PlutusIR.Check.Uniques qualified as Uniques
import PlutusIR.Core.Type
import PlutusIR.Error
import PlutusIR.TypeCheck qualified as TC

import PlutusCore qualified as PLC
import PlutusCore.Name

import Control.Monad (when)
import Control.Monad.Except
import Control.Monad.Trans.Class (lift)
import Data.Foldable
import Data.Text (Text)
import PlutusCore.Quote
import PlutusPrelude

-- | A condition on a 'Term'.
data Condition tyname name uni fun a where
  -- | The 'Term' typechecks.
  Typechecks :: (PLC.Typecheckable uni fun, PLC.GEq uni)
    => TC.PirTCConfig uni fun -> Condition TyName Name uni fun a
  -- | The 'Term' has globally unique names.
  GloballyUniqueNames :: (HasUnique tyname TypeUnique, HasUnique name TermUnique, Ord a)
    => Condition tyname name uni fun a
  -- | A custom condition.
  Custom :: (Term tyname name uni fun a -> Maybe (a, Text))
    -> Condition tyname name uni fun a

-- | A condition on a pair of 'Term's.
data BiCondition tyname name uni fun a where
  -- | A condition on the second 'Term'.
  ConstCondition :: Condition tyname name uni fun a -> BiCondition tyname name uni fun a
  -- | A custom condition.
  CustomBi :: (Term tyname name uni fun a -> Term tyname name uni fun a -> Maybe (a, Text))
    -> BiCondition tyname name uni fun a

checkCondition :: MonadError (Error uni fun a) m => Condition tyname name uni fun a -> Term tyname name uni fun a -> m ()
checkCondition c t = case c of
  Typechecks tcconfig -> void $ runQuoteT $ do
    -- Typechecking requires globally unique names
    renamed <- PLC.rename t
    TC.inferType tcconfig renamed
  GloballyUniqueNames -> void $ Uniques.checkTerm (const True) t
  Custom f -> case f t of
    Just (a, e) -> throwError $ CompilationError a e
    Nothing     -> pure ()

checkBiCondition :: MonadError (Error uni fun a) m => BiCondition tyname name uni fun a -> Term tyname name uni fun a -> Term tyname name uni fun a -> m ()
checkBiCondition c t1 t2 = case c of
  ConstCondition c' -> checkCondition c' t2
  CustomBi f -> case f t1 t2 of
    Just (a, e) -> throwError $ CompilationError a e
    Nothing     -> pure ()

-- | A pass over a term, with pre- and post-conditions.
data Pass m tyname name uni fun a =
  Pass String (Term tyname name uni fun a -> m (Term tyname name uni fun a)) [Condition tyname name uni fun a] [BiCondition tyname name uni fun a]
  | CompoundPass String [Pass m tyname name uni fun a]

passName :: Pass m tyname name uni fun a -> String
passName = \case
  Pass n _ _ _ -> n
  CompoundPass n _ -> n

preconditions :: Pass m tyname name uni fun a -> Maybe [Condition tyname name uni fun a]
preconditions = \case
  Pass _ _ p _ -> Just p
  CompoundPass{} -> Nothing

postcondtions :: Pass m tyname name uni fun a -> Maybe [BiCondition tyname name uni fun a]
postcondtions = \case
  Pass _ _ _ p -> Just p
  CompoundPass{} -> Nothing

hoistPass :: (forall v . m v -> n v) -> Pass m tyname name uni fun a -> Pass n tyname name uni fun a
hoistPass f p = case p of
  Pass n mainPass pre post -> Pass n (f . mainPass) pre post
  CompoundPass n passes    -> CompoundPass n (fmap (hoistPass f) passes)

runPass
  :: Monad m
  => (String -> m ())
  -> Bool
  -> Pass m tyname name uni fun a
  -> Term tyname name uni fun a
  -> ExceptT (Error uni fun a) m (Term tyname name uni fun a)
runPass logger checkConditions (Pass n mainPass pre post) t = do
  when checkConditions $ do
    lift $ logger $ n ++ ": checking preconditions"
    for_ pre $ \c -> checkCondition c t
  lift $ logger $ n ++ ": running pass"
  t' <- lift $ mainPass t
  when checkConditions $ do
    lift $ logger $ n ++ ": checking postconditions"
    for_ post $ \c -> checkBiCondition c t t'
  pure t'
runPass logger checkConditions (CompoundPass n passes) t = do
  lift $ logger $ n ++ ": running compound pass"
  let pfuns = map (runPass logger checkConditions) passes
  foldl' (>=>) pure pfuns t

-- | A simple, non-monadic pass that should typecheck.
simplePass
  :: (PLC.Typecheckable uni fun, PLC.GEq uni, Applicative m)
  => String
  -> TC.PirTCConfig uni fun
  -> (Term TyName Name uni fun a -> Term TyName Name uni fun a)
  -> Pass m TyName Name uni fun a
simplePass name tcConfig f = Pass name (pure . f) [Typechecks tcConfig] [ConstCondition (Typechecks tcConfig)]

-- | A pass that does renaming.
renamePass :: (HasUnique name TermUnique, HasUnique tyname TypeUnique, MonadQuote m, Ord a) => Pass m tyname name uni fun a
renamePass = Pass "renaming" PLC.rename [] [ConstCondition GloballyUniqueNames]
