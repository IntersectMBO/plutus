{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}

{-| Extract a module's UAL annotations at compile time.

The splice reads the enclosing module's own source file rather than GHC's comment
stream: @TH.location@ names the original @.hs@ path, and reading it needs no
exact-print annotations, no @Opt_KeepRawTokenStream@, and no dependence on how
GHC attaches comments to declarations. -}
module PlutusTx.Ual.TH
  ( ualModule
  , ualIdFor
  ) where

import Prelude

import Data.ByteString qualified as BS
import Data.Text qualified as Text
import Data.Text.Encoding qualified as Text
import Language.Haskell.TH qualified as TH
import Language.Haskell.TH.Syntax (addDependentFile, lift)
import PlutusTx.Blueprint.Definition (definitionId)
import PlutusTx.Ual.Error (UalError (..), renderUalError)
import PlutusTx.Ual.Parser (moduleUalFromSource, parseArgument)
import PlutusTx.Ual.Syntax
  ( ModuleUal (..)
  , OnchainDecl (..)
  , OnchainKind (..)
  , ResolvedArgument (..)
  , UalArgument (..)
  , UalModuleName (..)
  )

{-| Read the enclosing module's own source, extract its UAL blocks, resolve every
@ONCHAIN@ and @UPLC_DATA@ name, and splice in the resulting 'ModuleUal'.

Place this splice **after** every @ONCHAIN@ function and @UPLC_DATA@ type in the
module, and in a later declaration group than they are: the arity check reifies
each @ONCHAIN@ binding, and GHC only puts a binding in the type environment once
the group it belongs to has been type-checked. Being merely a later /declaration/
is not enough, because an expression splice does not start a new group. A
top-level declaration splice does, so an otherwise empty @$(pure [])@ above this
one is the usual way to get the boundary.

The source is decoded as UTF-8 rather than in the build machine's locale
encoding, because that is how GHC itself reads a @.hs@ file; an annotation
containing @∀@ would otherwise fail to decode under a non-UTF-8 locale.

@addDependentFile@ registers the file that was read with GHC's recompilation
checker. The path is always the module's own source, which GHC already tracks, so
the call does not change when this module is rebuilt; it is here so that the read
is declared rather than hidden inside @runIO@.

UAL blocks inside @#ifdef@ are read regardless of which branch CPP takes; blocks
under CPP are unsupported. -}
ualModule :: TH.Q TH.Exp
ualModule = do
  loc <- TH.location
  let path = TH.loc_filename loc
      fallback = UalModuleName (Text.pack (TH.loc_module loc))
  addDependentFile path
  src <- TH.runIO (Text.decodeUtf8 <$> BS.readFile path)
  m <- either die pure (moduleUalFromSource fallback src)
  mapM_ checkUplcData (ualUplcData m)
  onchainExps <- traverse onchainExp (ualOnchain m)
  [|
    MkModuleUal
      { ualModuleName = $(lift (ualModuleName m))
      , ualModuleImports = $(lift (ualModuleImports m))
      , ualOnchain = $(pure (TH.ListE onchainExps))
      , ualPredicates = $(lift (ualPredicates m))
      , ualProperties = $(lift (ualProperties m))
      , ualUplcData = $(lift (ualUplcData m))
      }
    |]

{-| The blueprint validator id for an @ONCHAIN@ function, as a 'Text' expression.
Agrees with 'PlutusTx.Ual.Resolve.onchainIdOf', which is identity on the name.

Use it instead of writing the id as a string literal: the annotation and the
blueprint entry then cannot drift, and a renamed function is a compile error
rather than a silently unmatched id. -}
ualIdFor :: TH.Name -> TH.Q TH.Exp
ualIdFor n = lift (Text.pack (TH.nameBase n))

----------------------------------------------------------------------------------------------------

{-| An 'OnchainDecl' as an expression: leaf fields lifted, @onchainResolvedArgs@
built from @definitionId \@T@ calls the compiler evaluates. -}
onchainExp :: OnchainDecl -> TH.Q TH.Exp
onchainExp d = do
  checkOnchain d
  args <- traverse resolvedArgExp (onchainArgs d)
  result <- case onchainKind d of
    Script -> [|Nothing|]
    Function -> do
      a <- either die pure (parseArgument (onchainLine d) (onchainResult d))
      r <- resolvedArgExp a
      [|Just $(pure r)|]
  [|
    MkOnchainDecl
      { onchainName = $(lift (onchainName d))
      , onchainKind = $(lift (onchainKind d))
      , onchainResolvedResult = $(pure result)
      , onchainArgs = $(lift (onchainArgs d))
      , onchainResult = $(lift (onchainResult d))
      , onchainVersion = $(lift (onchainVersion d))
      , onchainBudget = $(lift (onchainBudget d))
      , onchainLine = $(lift (onchainLine d))
      , onchainResolvedArgs = $(pure (TH.ListE args))
      }
    |]

{-| Resolve one argument's type name to a blueprint definition id.

This is where argument schemas are decided, rather than in
'PlutusTx.Ual.Resolve.attachUal': only the splice has the *type*, and only the
type gives the id. -}
resolvedArgExp :: UalArgument -> TH.Q TH.Exp
resolvedArgExp a = do
  ty <- typeOfName (argTypeName a)
  [|
    MkResolvedArgument
      { resolvedEncoding = $(lift (argEncoding a))
      , resolvedDefinitionId = definitionId @($(pure ty))
      }
    |]

{-| Turn an argument type as *written in the annotation* into a TH type.

Handles a plain name (@Ticket@) and a list of one (@[TxInInfo]@) — the two forms
UAL's own examples use. Anything more structured (tuples, applied type
constructors, @Map k v@) is rejected with a clear message rather than guessed at:
there is no TH parser for type syntax, so each form has to be built by hand, and
silently mis-resolving a type would produce a blueprint @$ref@ to the wrong
definition. -}
typeOfName :: Text.Text -> TH.Q TH.Type
typeOfName raw = case Text.stripPrefix "[" t >>= Text.stripSuffix "]" of
  Just inner -> TH.AppT TH.ListT <$> typeOfName (Text.strip inner)
  Nothing
    | Text.any (`elem` (" (),[]" :: String)) t ->
        die
          ( UnresolvedOnchainName
              t
              "only a plain type name or a list of one is supported in an ONCHAIN signature"
          )
    | otherwise ->
        TH.lookupTypeName (Text.unpack t) >>= \case
          Nothing -> die (UnresolvedOnchainName t "no such type is in scope at the splice")
          Just n -> pure (TH.ConT n)
  where
    t = Text.strip raw

{-| Spec §8.2 checks 1 and 2: the @ONCHAIN@ name exists, and the arity it
declares matches the arity of the Haskell binding. -}
checkOnchain :: OnchainDecl -> TH.Q ()
checkOnchain d = do
  let nameText = onchainName d
  TH.lookupValueName (Text.unpack nameText) >>= \case
    Nothing -> die (UnresolvedOnchainName nameText "no such value is in scope at the splice")
    Just n -> do
      actual <- arityOf n
      let declared = length (onchainArgs d)
      if actual /= declared
        then die (ArityMismatch nameText declared actual)
        else pure ()

-- | The number of arrows in a top-level binding's type.
arityOf :: TH.Name -> TH.Q Int
arityOf n =
  TH.reify n >>= \case
    TH.VarI _ ty _ -> pure (countArrows ty)
    other ->
      die
        ( UnresolvedOnchainName
            (Text.pack (TH.nameBase n))
            (Text.pack ("expected a value binding; reify gave " <> show other))
        )
  where
    countArrows = \case
      TH.ForallT _ _ t -> countArrows t
      TH.AppT (TH.AppT TH.ArrowT _) t -> 1 + countArrows t
      _ -> 0

{-| Spec §8.2 check 6: a @UPLC_DATA@ type must be in scope. Whether it has a
@HasBlueprintDefinition@ instance is checked by the caller's use of
@deriveDefinitions@, which is a type error if it does not — so this only needs to
catch a name that does not resolve at all. -}
checkUplcData :: Text.Text -> TH.Q ()
checkUplcData tyText =
  TH.lookupTypeName (Text.unpack tyText) >>= \case
    Nothing -> die (UnresolvedOnchainName tyText "no such type is in scope at the splice")
    Just _ -> pure ()

die :: UalError -> TH.Q a
die = fail . Text.unpack . renderUalError
