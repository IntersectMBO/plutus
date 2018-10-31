-- | Various views of PLC entities.

{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Language.PlutusCore.View
    ( IterApp(..)
    , TermIterApp
    , PrimIterApp
    , constantAsInteger
    , constantAsStagedBuiltinName
    , termAsConstant
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
type TermIterApp tyname name a =
    IterApp (Term tyname name a) (Term tyname name a)

-- | An iterated application of a 'BuiltinName' to a list of 'Value's.
type PrimIterApp tyname name a =
    IterApp StagedBuiltinName (Value tyname name a)

instance (PrettyBy config head, PrettyBy config arg) => PrettyBy config (IterApp head arg) where
    prettyBy config (IterApp appHead appSpine) =
        parens $ foldl' (\fun arg -> fun <+> prettyBy config arg) (prettyBy config appHead) appSpine

-- | View a 'Constant' as an 'Integer'.
constantAsInteger :: Constant a -> Maybe Integer
constantAsInteger (BuiltinInt _ _ int) = Just int
constantAsInteger _                    = Nothing

-- | View a 'Constant' as a 'StagedBuiltinName'.
constantAsStagedBuiltinName :: Constant a -> Maybe StagedBuiltinName
constantAsStagedBuiltinName (BuiltinName    _ name) = Just $ StaticStagedBuiltinName  name
constantAsStagedBuiltinName (DynBuiltinName _ name) = Just $ DynamicStagedBuiltinName name
constantAsStagedBuiltinName _                       = Nothing

-- | View a 'Term' as a 'Constant'.
termAsConstant :: Term tyname name a -> Maybe (Constant a)
termAsConstant (Constant _ constant) = Just constant
termAsConstant _                     = Nothing

-- | An iterated application of a 'Term' to a list of 'Term's.
termAsTermIterApp :: Term tyname name a -> TermIterApp tyname name a
termAsTermIterApp = go [] where
    go args (Apply _ fun arg) = go (arg : args) fun
    go args (TyInst _ fun _)  = go args fun
    go args  fun              = IterApp fun args

-- | View a 'Term' as an iterated application of a 'BuiltinName' to a list of 'Value's.
termAsPrimIterApp :: Term tyname name a -> Maybe (PrimIterApp tyname name a)
termAsPrimIterApp term = do
    let IterApp termHead spine = termAsTermIterApp term
    headName <- termAsConstant termHead >>= constantAsStagedBuiltinName
    guard $ all isValue spine
    Just $ IterApp headName spine

-- | Check whether a 'Term' is a 'Value'.
isValue :: Term tyname name a -> Bool
isValue (TyAbs  _ _ _ body)  = isValue body
isValue (IWrap _ _ _ _ term) = isValue term
isValue LamAbs{}             = True
isValue Constant{}           = True
isValue term                 = isJust $ termAsPrimIterApp term
