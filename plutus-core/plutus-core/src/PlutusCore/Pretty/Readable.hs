{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

-- | A "readable" Agda-like way to pretty-print PLC entities.
module PlutusCore.Pretty.Readable
  ( module Export
  , module PlutusCore.Pretty.Readable
  ) where

import PlutusPrelude

import PlutusCore.Pretty.ConfigName
import PlutusCore.Pretty.Extra as Export

import Control.Lens
import Data.Profunctor as Export (Profunctor (..))
import Prettyprinter.Custom
import Text.Pretty
import Text.PrettyBy.Default
import Text.PrettyBy.Fixity as Export
import Text.PrettyBy.Internal

data ShowKinds
  = ShowKindsYes
  | ShowKindsNonType
  | ShowKindsNo
  deriving stock (Show, Eq)

instance Default ShowKinds where
  def = ShowKindsNonType

-- | Configuration for the readable pretty-printing.
data PrettyConfigReadable configName = PrettyConfigReadable
  { _pcrConfigName :: configName
  , _pcrRenderContext :: RenderContext
  , _pcrShowKinds :: ShowKinds
  }
  deriving stock (Show)

type instance HasPrettyDefaults (PrettyConfigReadable _) = 'True

-- | The "readably pretty-printable" constraint.
type PrettyReadableBy configName = PrettyBy (PrettyConfigReadable configName)

type PrettyReadable = PrettyReadableBy PrettyConfigName

{-| A constraint for \"@m@ is a monad that allows for pretty-printing values via a
'PrettyConfigReadable'. -}
type MonadPrettyReadable configName env m = MonadPretty (PrettyConfigReadable configName) env m

type HasPrettyConfigReadable env configName =
  HasPrettyConfig env (PrettyConfigReadable configName)

makeLenses ''PrettyConfigReadable

instance
  configName ~ PrettyConfigName
  => HasPrettyConfigName (PrettyConfigReadable configName)
  where
  toPrettyConfigName = _pcrConfigName

instance HasRenderContext (PrettyConfigReadable configName) where
  renderContext = pcrRenderContext

{-| For rendering things in a readable manner regardless of the pretty-printing function chosen.
I.e. all of 'show', 'pretty', 'prettyClassic' will use 'PrettyReadable' instead of doing what
they normally do. @prettyBy config (AsReadable x)@ requires @config@ to have a 'PrettyConfigName'
and respects it.

This wrapper can be particularly useful if you want to apply a function having a 'Show' or
'Pretty' or 'PrettyClassic' or 'PrettyPlc' or whatever constraint, but want to get the argument
rendered in a readable manner instead. -}
newtype AsReadable a = AsReadable
  { unAsReadable :: a
  }

instance
  (HasPrettyConfigName config, PrettyReadable a)
  => DefaultPrettyBy config (AsReadable a)
  where
  defaultPrettyBy config (AsReadable x) =
    prettyBy (botPrettyConfigReadable (toPrettyConfigName config) def) x

instance PrettyReadable a => Show (AsReadable a) where
  show = displayBy $ Sole prettyConfigName

instance PrettyReadable a => Pretty (AsReadable a) where
  pretty = viaShow

deriving via
  PrettyCommon (AsReadable a)
  instance
    PrettyDefaultBy config (AsReadable a) => PrettyBy config (AsReadable a)

-- | A value of type @a@ to render in parens using the readable pretty-printer.
data Parened a = Parened
  { parenOpening :: String
  , parenClosing :: String
  , parenedValue :: a
  }

instance
  PrettyReadableBy configName a
  => PrettyBy (PrettyConfigReadable configName) (Parened a)
  where
  prettyBy config (Parened opening closing x) =
    fold
      [ pretty opening
      , prettyBy (config & renderContext .~ botRenderContext) x
      , pretty closing
      ]

{-| Enclose the given value, so that it's rendered inside of braces with no additional parens
regardless of the 'RenderContext'. -}
inBraces :: a -> Parened a
inBraces = Parened "{" "}"

-- | A 'PrettyConfigReadable' with the fixity specified to 'botFixity'.
botPrettyConfigReadable :: configName -> ShowKinds -> PrettyConfigReadable configName
botPrettyConfigReadable configName = PrettyConfigReadable configName botRenderContext

-- | A 'PrettyConfigReadable' with the fixity specified to 'topFixity'.
topPrettyConfigReadable :: configName -> ShowKinds -> PrettyConfigReadable configName
topPrettyConfigReadable configName = PrettyConfigReadable configName topRenderContext

-- | The fixity of a binder.
binderFixity :: Fixity
binderFixity = Fixity RightAssociative 1

-- | The fixity of @(->)@.
arrowFixity :: Fixity
arrowFixity = Fixity RightAssociative 2

{-| Lay out an iterated binder. For example, this function lays out iterated lambdas either as

> \(x : a) (y : b) (z : c) -> body

or as

> \(x : a)
>  (y : b)
>  (z : c) ->
>   body -}
iterBinderPrettyM
  :: ( MonadPrettyReadable configName env m
     , PrettyReadableBy configName arg
     , PrettyReadableBy configName body
     )
  => (Doc ann -> Doc ann)
  -> [arg]
  -> body
  -> m (Doc ann)
iterBinderPrettyM enframe args body =
  infixDocM binderFixity $ \prettyBind prettyBody ->
    let prettyBinds = align . sep $ map prettyBind args
     in enframe prettyBinds <?> prettyBody body

-- | Lay out an iterated 'TyForall' via 'iterBinderPrettyM'.
iterTyForallPrettyM
  :: ( MonadPrettyReadable configName env m
     , PrettyReadableBy configName arg
     , PrettyReadableBy configName body
     )
  => [arg]
  -> body
  -> m (Doc ann)
iterTyForallPrettyM = iterBinderPrettyM $ \binds -> "all" <+> binds <> "."

-- | Lay out an iterated 'LamAbs' via 'iterBinderPrettyM'.
iterLamAbsPrettyM
  :: ( MonadPrettyReadable configName env m
     , PrettyReadableBy configName arg
     , PrettyReadableBy configName body
     )
  => [arg]
  -> body
  -> m (Doc ann)
iterLamAbsPrettyM = iterBinderPrettyM $ \binds -> "\\" <> binds <+> "->"

-- | Lay out an iterated 'TyAbs' via 'iterBinderPrettyM'.
iterTyAbsPrettyM
  :: ( MonadPrettyReadable configName env m
     , PrettyReadableBy configName arg
     , PrettyReadableBy configName body
     )
  => [arg]
  -> body
  -> m (Doc ann)
iterTyAbsPrettyM = iterBinderPrettyM $ \binds -> "/\\" <> binds <+> "->"

-- | Lay out an iterated @->@.
iterArrowPrettyM
  :: (MonadPrettyReadable configName env m, PrettyReadableBy configName a)
  => [a]
  -> a
  -> m (Doc ann)
iterArrowPrettyM args res =
  infixDocM arrowFixity $ \prettyArg prettyRes ->
    align . sep $ map (\x -> prettyArg x <+> "->") args ++ [prettyRes res]

-- | The type of a 'PrettyConfigReadable'-based pretty-printer, similar to 'AnyToDoc'.
type ReadableToDoc configName ann = forall a. PrettyReadableBy configName a => a -> Doc ann

{-| Lay out an iteration application, providing to the caller a function to render the head of the
application and a function to render each of the arguments. -}
iterAppDocM
  :: MonadPrettyContext config env m
  => (AnyToDoc config ann -> AnyToDoc config ann -> NonEmpty (Doc ann))
  -> m (Doc ann)
iterAppDocM k =
  infixDocM juxtFixity $ \prettyFun prettyArg ->
    let fun :| args = k prettyFun prettyArg
     in if null args
          then fun
          else fun <?> vsep args

{-| Lay out iterated function applications either as

> foo x y z

or as

> foo
>   x
>   y
>   z -}
iterAppPrettyM
  :: ( MonadPrettyContext config env m
     , PrettyBy config fun
     , PrettyBy config term
     )
  => fun
  -> [term]
  -> m (Doc ann)
iterAppPrettyM fun args =
  iterAppDocM $ \prettyFun prettyArg ->
    prettyFun fun :| map prettyArg args

{-| Lay out interleaved function applications either as

> foo {a} x {b} y z

or as

> foo
>   {a}
>   x
>   {b}
>   y
>   z

'Left's are laid out in braces, 'Right's are laid out without braces. -}
iterInterAppPrettyM
  :: ( MonadPrettyReadable configName env m
     , PrettyReadableBy configName fun
     , PrettyReadableBy configName ty
     , PrettyReadableBy configName term
     )
  => fun
  -> [Either ty term]
  -> m (Doc ann)
iterInterAppPrettyM fun args =
  iterAppDocM $ \prettyFun prettyArg ->
    let ppArg (Left ty) = prettyArg $ inBraces ty
        ppArg (Right term) = prettyArg term
     in prettyFun fun :| map ppArg args

-- | Pretty-print something with the @PrettyConfigReadable@ config.
prettyReadable :: PrettyReadable a => a -> Doc ann
prettyReadable = prettyBy (botPrettyConfigReadable prettyConfigName def)

-- | Pretty-print something with the @PrettyConfigReadableSimple@ config.
prettyReadableSimple :: PrettyReadable a => a -> Doc ann
prettyReadableSimple = prettyBy (botPrettyConfigReadable prettyConfigNameSimple def)
