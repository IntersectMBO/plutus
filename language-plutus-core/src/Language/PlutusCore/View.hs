-- | Various views of PLC entities.

{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Language.PlutusCore.View
    ( IterApp(..)
    , TermIterApp
    , PrimIterApp
    , constantAsStagedBuiltinName
    , termAsBuiltin
    , termAsTermIterApp
    , termAsPrimIterApp
    ) where

import           Language.PlutusCore.Lexer.Type (StagedBuiltinName (..))
import           Language.PlutusCore.Type
import           PlutusPrelude

-- | A function (called "head") applied to a list of arguments (called "spine").
data IterApp head arg = IterApp
    { _iterAppHead  :: head
    , _iterAppSpine :: [arg]
    }

-- | An iterated application of a 'Term' to a list of 'Term's.
type TermIterApp tyname name uni ann =
    IterApp (Term tyname name uni ann) (Term tyname name uni ann)

-- | An iterated application of a 'BuiltinName' to a list of 'Value's.
type PrimIterApp tyname name uni ann =
    IterApp StagedBuiltinName (Value tyname name uni ann)

instance (PrettyBy config head, PrettyBy config arg) => PrettyBy config (IterApp head arg) where
    prettyBy config (IterApp appHead appSpine) =
        parens $ foldl' (\fun arg -> fun <+> prettyBy config arg) (prettyBy config appHead) appSpine

-- | View a 'Constant' as a 'StagedBuiltinName'.
constantAsStagedBuiltinName :: Builtin ann -> StagedBuiltinName
constantAsStagedBuiltinName (BuiltinName    _ name) = StaticStagedBuiltinName  name
constantAsStagedBuiltinName (DynBuiltinName _ name) = DynamicStagedBuiltinName name

-- | View a 'Term' as a 'Constant'.
termAsBuiltin :: Term tyname name uni ann -> Maybe (Builtin ann)
termAsBuiltin (Builtin _ bi) = Just bi
termAsBuiltin _              = Nothing

-- | An iterated application of a 'Term' to a list of 'Term's.
termAsTermIterApp :: Term tyname name uni ann -> TermIterApp tyname name uni ann
termAsTermIterApp = go [] where
    go args (Apply _ fun arg) = go (arg : args) fun
    go args (TyInst _ fun _)  = go args fun
    go args fun               = IterApp fun args

-- | View a 'Term' as an iterated application of a 'BuiltinName' to a list of 'Value's.
termAsPrimIterApp :: Term tyname name uni ann -> Maybe (PrimIterApp tyname name uni ann)
termAsPrimIterApp term = do
    let IterApp termHead spine = termAsTermIterApp term
    headName <- constantAsStagedBuiltinName <$> termAsBuiltin termHead
    -- This is commented out for two reasons:
    -- 1. we use 'termAsPrimIterApp' in abstract machines and we may not want to have this overhead
    -- 2. 'Error' is not a value, but we can return 'Error' from a failed constant application
    --    and then this function incorrectly returns 'Nothing' instead of indicating that an error
    --    has occurred or doing something else that makes sense.
    -- TODO: resolve this.
    -- guard $ all isTermValue spine
    Just $ IterApp headName spine
