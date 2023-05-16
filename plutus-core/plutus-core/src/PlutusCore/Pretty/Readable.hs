-- editorconfig-checker-disable-file
-- | A "readable" Agda-like way to pretty-print PLC entities.

{-# LANGUAGE ConstraintKinds       #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE UndecidableInstances  #-}

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
    { _pcrConfigName    :: configName
    , _pcrRenderContext :: RenderContext
    , _pcrShowKinds     :: ShowKinds
    }

type instance HasPrettyDefaults (PrettyConfigReadable _) = 'True

-- | The "readably pretty-printable" constraint.
type PrettyReadableBy configName = PrettyBy (PrettyConfigReadable configName)

type PrettyReadable = PrettyReadableBy PrettyConfigName

type HasPrettyConfigReadable env configName =
    HasPrettyConfig env (PrettyConfigReadable configName)

makeLenses ''PrettyConfigReadable

instance configName ~ PrettyConfigName =>
        HasPrettyConfigName (PrettyConfigReadable configName) where
    toPrettyConfigName = _pcrConfigName

instance HasRenderContext (PrettyConfigReadable configName) where
    renderContext = pcrRenderContext

-- | For rendering things in a readable manner regardless of the pretty-printing function chosen.
-- I.e. all of 'show', 'pretty', 'prettyClassicDef' will use 'PrettyReadable' instead of doing what
-- they normally do. @prettyBy config (AsReadable x)@ requires @config@ to have a 'PrettyConfigName'
-- and respects it.
--
-- This wrapper can be particularly useful if you want to apply a function having a 'Show' or
-- 'Pretty' or 'PrettyClassic' or 'PrettyPlc' or whatever constraint, but want to get the argument
-- rendered in a readable manner instead.
newtype AsReadable a = AsReadable
    { unAsReadable :: a
    }

instance (HasPrettyConfigName config, PrettyReadable a) =>
        DefaultPrettyBy config (AsReadable a) where
    defaultPrettyBy config (AsReadable x) =
        prettyBy (topPrettyConfigReadable (toPrettyConfigName config) def) x

instance PrettyReadable a => Show (AsReadable a) where
    show = displayBy $ Sole defPrettyConfigName

instance PrettyReadable a => Pretty (AsReadable a) where
    pretty = viaShow

deriving via PrettyCommon (AsReadable a)
    instance PrettyDefaultBy config (AsReadable a) => PrettyBy config (AsReadable a)

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

-- | Pretty-print two things with a @->@ between them.
arrowPrettyM
    :: (MonadPrettyContext config env m, PrettyBy config a, PrettyBy config b)
    => a -> b -> m (Doc ann)
arrowPrettyM a b =
    infixDocM arrowFixity $ \prettyL prettyR -> prettyL a <+> "->" <+> prettyR b

-- | Lay out an iterated binder. For example, this function lays out iterated lambdas either as
--
-- > \(x : a) (y : b) (z : c) -> body
--
-- or as
--
-- > \(x : a)
-- >  (y : b)
-- >  (z : c) ->
-- >   body
iterBinderPrettyM
    :: ( MonadPrettyContext config env m
       , PrettyBy config arg, PrettyBy config body
       )
    => (Doc ann -> Doc ann) -> [arg] -> body -> m (Doc ann)
iterBinderPrettyM enframe args body =
    -- TODO: should this be @infixDocM binderFixity@?
    compoundDocM binderFixity $ \prettyIn ->
        let prettyBot x = prettyIn ToTheRight botFixity x
            prettyBinds = align . vsep $ map (prettyIn ToTheLeft binderFixity) args
        in enframe prettyBinds <?> prettyBot body

-- | Lay out an iterated 'TyForall' via 'iterBinderPrettyM'.
iterTyForallPrettyM
    :: ( MonadPrettyContext config env m
       , PrettyBy config arg, PrettyBy config body
       )
    => [arg] -> body -> m (Doc ann)
iterTyForallPrettyM = iterBinderPrettyM $ \binds -> "all" <+> binds <> "."

-- | Lay out an iterated 'LamAbs' via 'iterBinderPrettyM'.
iterLamAbsPrettyM
    :: ( MonadPrettyContext config env m
       , PrettyBy config arg, PrettyBy config body
       )
    => [arg] -> body -> m (Doc ann)
iterLamAbsPrettyM = iterBinderPrettyM $ \binds -> "\\" <> binds <+> "->"

-- | Lay out an iterated 'TyAbs' via 'iterBinderPrettyM'.
iterTyAbsPrettyM
    :: ( MonadPrettyContext config env m
       , PrettyBy config arg, PrettyBy config body
       )
    => [arg] -> body -> m (Doc ann)
iterTyAbsPrettyM = iterBinderPrettyM $ \binds -> "/\\" <> binds <+> "->"

-- | Lay out interleaved function applications either as
--
-- > foo {a} x {b} y z
--
-- or as
--
-- > foo
-- >   {a}
-- >   x
-- >   {b}
-- >   y
-- >   z
--
-- 'Left's are laid out in braces, 'Right's are laid out without braces.
iterAppPrettyM
    :: ( MonadPrettyContext config env m
       , PrettyBy config fun, PrettyBy config ty, PrettyBy config term
       )
    => fun -> [Either ty term] -> m (Doc ann)
iterAppPrettyM fun args =
    compoundDocM juxtFixity $ \prettyIn ->
        let ppArg (Left a)  = braces $ prettyIn ToTheRight botFixity a
            ppArg (Right t) = prettyIn ToTheRight juxtFixity t
        in prettyIn ToTheLeft juxtFixity fun <?> vsep (map ppArg args)
