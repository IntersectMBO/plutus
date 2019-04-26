-- | A "readable" Agda-like way to pretty-print PLC entities.

{-# LANGUAGE ConstraintKinds       #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE UndecidableInstances  #-}

module Language.PlutusCore.Pretty.Readable
    ( RenderContext (..)
    , ShowKinds (..)
    , PrettyConfigReadable (..)
    , PrettyReadableBy
    , PrettyReadable
    , topPrettyConfigReadable
    , botPrettyConfigReadable
    ) where

import           Language.PlutusCore.Lexer.Type     hiding (name)
import           Language.PlutusCore.Name
import           Language.PlutusCore.Type
import           PlutusPrelude

import           Data.Text.Prettyprint.Doc.Internal (enclose)

-- | Associativity of an expression.
data Associativity
    = LeftAssociative
    | RightAssociative
    | NonAssociative
    deriving (Eq)

-- | Fixity of an expression.
data Fixity = Fixity
    { _fixityPrecedence    :: Natural
    , _fixityAssociativity :: Associativity
    }

-- | Determines whether we're going to the right of an operator or to the left.
data Direction
    = Forward   -- ^ To the right.
    | Backward  -- ^ To the left.
    deriving (Eq)

-- | A context an expression is rendering in.
data RenderContext = RenderContext
    { _rcDirection :: Direction
    , _rcFixity    :: Fixity
    }

data ShowKinds
    = ShowKindsYes
    | ShowKindsNo
    deriving (Show, Eq)

-- | Configuration for the readable pretty-printing.
data PrettyConfigReadable configName = PrettyConfigReadable
    { _pcrConfigName    :: configName
    , _pcrRenderContext :: RenderContext
    , _pcrShowKinds     :: ShowKinds
    }

instance configName ~ PrettyConfigName => HasPrettyConfigName (PrettyConfigReadable configName) where
    toPrettyConfigName = _pcrConfigName

-- | A fixity with the lowest precedence.
-- When used as a part of an outer context, never causes the addition of parens.
botApp :: Fixity
botApp = Fixity 0 NonAssociative

-- | The fixity of a binder.
binderApp :: Fixity
binderApp = Fixity 1 RightAssociative

-- | The fixity of @(->)@.
arrowApp :: Fixity
arrowApp = Fixity 2 RightAssociative

-- | The fixity of juxtaposition.
juxtApp :: Fixity
juxtApp = Fixity 10 LeftAssociative

-- | The fixity of a unitary expression which is safe to render
-- without parens in any context.
unitApp :: Fixity
unitApp = Fixity 11 NonAssociative

-- | A fixity with the highest precedence.
-- When used as a part of an outer context, always causes the addition of parens.
topApp :: Fixity
topApp = Fixity 12 NonAssociative

-- | A 'PrettyConfigReadable' with the fixity specified to 'topApp'.
topPrettyConfigReadable :: configName -> ShowKinds -> PrettyConfigReadable configName
topPrettyConfigReadable configName = PrettyConfigReadable configName $ RenderContext Forward topApp

-- | A 'PrettyConfigReadable' with the fixity specified to 'botApp'.
botPrettyConfigReadable :: configName -> ShowKinds -> PrettyConfigReadable configName
botPrettyConfigReadable configName = PrettyConfigReadable configName $ RenderContext Forward botApp

-- | Set the 'RenderContext' of a 'PrettyConfigReadable'.
setRenderContext :: RenderContext -> PrettyConfigReadable configName -> PrettyConfigReadable configName
setRenderContext context configReadable = configReadable { _pcrRenderContext = context }

-- | Enclose a 'Doc' in parens if required or leave it as is.
-- The need for enclosing is determined from an outer 'RenderContext' and the 'Doc's fixity.
encloseInContext
    :: RenderContext  -- ^ An outer context.
    -> Fixity         -- ^ An inner fixity.
    -> Doc ann
    -> Doc ann
encloseInContext (RenderContext dir (Fixity precOut assocOut)) (Fixity precIn assocIn) =
    case precOut `compare` precIn of
        LT -> id                      -- If the outer precedence is lower than the inner, then
                                      -- do not add parens. E.g. in @Add x (Mul y z)@ the precedence
                                      -- of @Add@ is lower than the one of @Mul@, hence there is
                                      -- no need for parens in @x + y * z@.
        GT -> parens                  -- If the outer precedence is greater than the inner, then
                                      -- do add parens. E.g. in @Mul x (Add y z)@ the precedence
                                      -- of @Mul@ is greater than the one of @Add@, hence
                                      -- parens are needed in @x * (y + z)@.
        EQ ->                         -- If precedences are equal, then judge from associativity.
            case (assocOut, dir) of
                _ | assocOut /= assocIn     -> parens  -- Associativities differ => parens are needed.
                (LeftAssociative, Backward) -> id      -- No need for parens in @Add (Add x y) z@
                                                       -- which is rendered as @x + y + z@.
                (RightAssociative, Forward) -> id      -- No need for parens in @Concat xs (Concat xs zs)@
                                                       -- which is rendered as @xs ++ ys ++ zs@.
                _                           -> parens  -- Every other case requires parens.

-- | The "readably pretty-printable" constraint.
type PrettyReadableBy configName = PrettyBy (PrettyConfigReadable configName)

type PrettyReadable = PrettyReadableBy PrettyConfigName

type AnyToDocBy configName ann = forall a. PrettyReadableBy configName a => a -> Doc ann

-- | Adjust a 'PrettyConfigReadable' by setting new 'Fixity' and 'Direction' and call 'prettyBy'.
prettyInBy
    :: PrettyReadableBy configName a
    => PrettyConfigReadable configName -> Direction -> Fixity -> a -> Doc ann
prettyInBy config dir app = prettyBy $ setRenderContext (RenderContext dir app) config

-- | Pretty-print in 'botApp'.
prettyInBotBy :: PrettyReadableBy configName a => PrettyConfigReadable configName -> a -> Doc ann
prettyInBotBy config = prettyInBy config Forward botApp

-- | Call 'encloseInContext' on 'unitApp'.
unitaryDoc :: PrettyConfigReadable configName -> Doc ann -> Doc ann
unitaryDoc config = encloseInContext (_pcrRenderContext config) unitApp

-- | Instantiate a supplied continuation with a pretty-printer specialized to the supplied
-- 'Fixity' and apply 'encloseInContext', specialized to the same 'Fixity', to the result.
rayDoc
    :: PrettyConfigReadable configName
    -> Direction
    -> Fixity
    -> (AnyToDocBy configName ann -> Doc ann)
    -> Doc ann
rayDoc config dir app k =
    encloseInContext (_pcrRenderContext config) app $
        k (prettyInBy config dir app)

-- | 'rayDoc' specialized to 'binderApp'.
binderDoc
    :: PrettyConfigReadable configName
    -> (AnyToDocBy configName ann -> Doc ann)
    -> Doc ann
binderDoc config = rayDoc config Forward binderApp
-- This perhaps makes less sense than 'compoundDoc', because to the outside binders
-- can look differently than how they look to the inside, but whatever.
-- This applies to 'rayDoc' in general.

-- | Instantiate a supplied continuation with two pretty-printers (one is going in the 'Backward'
-- direction, the other is in the 'Forward' direction) specialized to the supplied 'Fixity'
-- and apply 'encloseInContext', specialized to the same 'Fixity', to the result.
-- The idea is that to the outside an expression has the same inner fixity as
-- it has the outer fixity to inner subexpressions.
compoundDoc
    :: PrettyConfigReadable configName
    -> Fixity
    -> (AnyToDocBy configName ann -> AnyToDocBy configName ann -> Doc ann)
    -> Doc ann
compoundDoc config app k =
    encloseInContext (_pcrRenderContext config) app $
        k (prettyInBy config Backward app) (prettyInBy config Forward app)

-- | Pretty-print an application of a function to its argument.
applicationDoc
    :: (PrettyReadableBy configName a, PrettyReadableBy configName b)
    => PrettyConfigReadable configName -> a -> b -> Doc ann
applicationDoc config fun arg =
    compoundDoc config juxtApp $ \juxtL juxtR -> juxtL fun <+> juxtR arg

-- | Pretty-print a @->@ between two things.
arrowDoc
    :: (PrettyReadableBy configName a, PrettyReadableBy configName b)
    => PrettyConfigReadable configName -> a -> b -> Doc ann
arrowDoc config a b =
    compoundDoc config arrowApp $ \arrL arrR -> arrL a <+> "->" <+> arrR b

-- | Pretty-print a binding at the type level.
prettyTypeBinding
    :: PrettyReadableBy configName (tyname a)
    => PrettyConfigReadable configName -> tyname a -> Kind a -> Doc ann
prettyTypeBinding config name kind
    | _pcrShowKinds config == ShowKindsYes = parens $ prName <+> "::" <+> prettyInBotBy config kind
    | otherwise                            = prName
    where prName = prettyBy config name

instance PrettyBy (PrettyConfigReadable configName) (Kind a) where
    prettyBy config = \case
        Type{}          -> unitaryDoc config "*"
        KindArrow _ k l -> arrowDoc   config k l

instance PrettyBy (PrettyConfigReadable configName) (Constant a) where
    prettyBy config = unitaryDoc config . \case
        BuiltinInt _ int -> pretty int
        BuiltinBS _ bs   -> prettyBytes bs
        BuiltinStr _ str      -> pretty str

instance PrettyBy (PrettyConfigReadable configName) (Builtin a) where
    prettyBy config = unitaryDoc config . \case
        BuiltinName    _ name -> pretty name
        DynBuiltinName _ name -> pretty name

instance PrettyReadableBy configName (tyname a) =>
        PrettyBy (PrettyConfigReadable configName) (Type tyname a) where
    prettyBy config = \case
        TyApp _ fun arg         -> applicationDoc config fun arg
        TyVar _ name            -> unit $ prettyName name
        TyFun _ tyIn tyOut      -> arrowDoc config tyIn tyOut
        TyIFix _ pat arg        -> rayR juxtApp $ \juxt -> "ifix" <+> juxt pat <+> juxt arg
        TyForall _ name kind ty -> bind $ \bindBody ->
            "all" <+> prettyTypeBinding config name kind <> "." <+> bindBody ty
        TyBuiltin _ builtin     -> unit $ pretty builtin
        TyLam _ name kind ty    -> bind $ \bindBody ->
            "\\" <> prettyTypeBinding config name kind <+> "->" <+> bindBody ty
      where
        prettyName = prettyBy config
        unit = unitaryDoc config
        rayR = rayDoc config Forward
        bind = binderDoc  config

instance (PrettyReadableBy configName (tyname a), PrettyReadableBy configName (name a)) =>
        PrettyBy (PrettyConfigReadable configName) (Term tyname name a) where
    prettyBy config = \case
        Constant _ con         -> prettyBy config con
        Builtin _ bi           -> prettyBy config bi
        Apply _ fun arg        -> applicationDoc config fun arg
        Var _ name             -> unit $ prettyName name
        TyAbs _ name kind body -> bind $ \bindBody ->
            "/\\" <> prettyTypeBinding config name kind <+> "->" <+> bindBody body
        TyInst _ fun ty        -> rayL juxtApp $ \juxt -> juxt fun <+> inBraces ty
        LamAbs _ name ty body  -> bind $ \bindBody ->
            "\\" <> parens (prettyName name <+> ":" <+> inBot ty) <+> "->" <+> bindBody body
        Unwrap _ term          -> rayR juxtApp $ \juxt -> "unwrap" <+> juxt term
        IWrap _ pat arg term   -> rayR juxtApp $ \juxt ->
            "iwrap" <+> juxt pat <+> juxt arg <+> juxt term
        Error _ ty             -> comp juxtApp $ \_ _ -> "error" <+> inBraces ty
      where
        prettyName = prettyBy config
        unit = unitaryDoc  config
        bind = binderDoc   config
        rayL = rayDoc      config Backward
        rayR = rayDoc      config Forward
        comp = compoundDoc config
        inBot    = prettyInBotBy config
        inBraces = enclose "{" "}" . inBot

instance PrettyReadableBy configName (Term tyname name a) =>
        PrettyBy (PrettyConfigReadable configName) (Program tyname name a) where
    prettyBy config (Program _ version term) =
        rayDoc config Forward juxtApp $ \juxt -> "program" <+> pretty version <+> juxt term
