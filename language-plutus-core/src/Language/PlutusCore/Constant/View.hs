module Language.PlutusCore.Constant.View
    ( IterApp(..)
    , TermIterApp
    , PrimIterApp
    , viewBuiltinName
    , viewConstant
    , viewTermIterApp
    , viewPrimIterApp
    ) where

import           Language.PlutusCore.Lexer.Type (BuiltinName(..))
import           Language.PlutusCore.Type

-- | A function (called "head") applied to a list of arguments (called "spine").
data IterApp head arg = IterApp
    { _iterAppHead  :: head
    , _iterAppSpine :: [arg]
    }

type TermIterApp tyname name a =
    IterApp (Term tyname name a) (Term tyname name a)

type PrimIterApp =
    IterApp BuiltinName (Constant ())

-- | View a `Constant` as a `BuiltinName`.
viewBuiltinName :: Constant a -> Maybe BuiltinName
viewBuiltinName (BuiltinName _ name) = Just name
viewBuiltinName _                    = Nothing

-- | View a `Term` as a `Constant`.
viewConstant :: Term tyname name a -> Maybe (Constant a)
viewConstant (Constant _ constant) = Just constant
viewConstant _                     = Nothing

-- | View a `Term` as an `IterApp`.
viewTermIterApp :: Term tyname name a -> Maybe (TermIterApp tyname name a)
viewTermIterApp term@Apply{} = Just $ go [] term where
    go args (Apply _ fun arg) = go (undefined arg : args) fun
    go args  fun              = IterApp fun args
viewTermIterApp _            = Nothing

-- | View a `Term` as an iterated application of a `BuiltinName` to a list of `Constants`.
viewPrimIterApp :: Term tyname name () -> Maybe PrimIterApp
viewPrimIterApp term = do
    IterApp termHead termSpine <- viewTermIterApp term
    headName <- viewConstant termHead >>= viewBuiltinName
    spine <- traverse viewConstant termSpine
    Just $ IterApp headName spine
