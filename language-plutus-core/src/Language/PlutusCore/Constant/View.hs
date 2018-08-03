module Language.PlutusCore.Constant.View
    ( IterApp(..)
    , TermIterApp
    , PrimIterApp
    , viewBuiltinInt
    , viewBuiltinName
    , viewConstant
    , viewTermIterApp
    , viewPrimIterApp
    ) where

import           PlutusPrelude
import           Language.PlutusCore.Lexer.Type (BuiltinName(..))
import           Language.PlutusCore.Type
import           Language.PlutusCore.Constant.Prelude

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
    IterApp BuiltinName (Value tyname name a)

-- | View a 'Constant' as an 'Integer'.
viewBuiltinInt :: Constant a -> Maybe Integer
viewBuiltinInt (BuiltinInt _ _ int) = Just int
viewBuiltinInt _                    = Nothing

-- | View a 'Constant' as a 'BuiltinName'.
viewBuiltinName :: Constant a -> Maybe BuiltinName
viewBuiltinName (BuiltinName _ name) = Just name
viewBuiltinName _                    = Nothing

-- | View a 'Term' as a 'Constant'.
viewConstant :: Term tyname name a -> Maybe (Constant a)
viewConstant (Constant _ constant) = Just constant
viewConstant _                     = Nothing

-- | An iterated application of a 'Term' to a list of 'Term's.
viewTermIterApp :: Term tyname name a -> Maybe (TermIterApp tyname name a)
viewTermIterApp term@Apply{} = Just $ go [] term where
    go args (Apply _ fun arg) = go (undefined arg : args) fun
    go args (TyInst _ fun _)  = go args fun
    go args  fun              = IterApp fun args
viewTermIterApp _            = Nothing

-- | View a 'Term' as an iterated application of a 'BuiltinName' to a list of 'Value's.
viewPrimIterApp :: Term tyname name a -> Maybe (PrimIterApp tyname name a)
viewPrimIterApp term = do
    IterApp termHead spine <- viewTermIterApp term
    headName <- viewConstant termHead >>= viewBuiltinName
    guard $ all isValue spine
    Just $ IterApp headName spine

-- | Check whether a 'Term' is a 'Value'.
isValue :: Term tyname name a -> Bool
isValue (TyAbs  _ _ _ body) = isValue body
isValue (Wrap   _ _ _ term) = isValue term
isValue (LamAbs _ _ _ body) = isValue body
isValue (Constant _ _)      = True
isValue  term               = isJust $ viewPrimIterApp term
