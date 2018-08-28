{-# LANGUAGE DeriveLift          #-}
{-# LANGUAGE QuasiQuotes         #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving  #-}
{-# LANGUAGE TemplateHaskell     #-}
{-# LANGUAGE TypeApplications    #-}

module Language.PlutusCore.TH (plcTerm, plcType, plcProgram) where

import           Language.Haskell.TH        hiding (Name, Type)
import           Language.Haskell.TH.Quote

import           Language.PlutusCore        (discardAnnsTerm, discardAnnsTy)
import           Language.PlutusCore.Name
import           Language.PlutusCore.Parser (ParseError)
import           Language.PlutusCore.Quote
import           Language.PlutusCore.Subst
import           Language.PlutusCore.Type

import           PlutusPrelude

import           Control.Monad.Except
import qualified Data.ByteString.Lazy       as BSL
import           Data.Functor.Identity
import qualified Data.Map                   as Map
import qualified Data.Set                   as Set

{-
This uses the approach in https://www.well-typed.com/blog/2014/10/quasi-quoting-dsls/ to use free
object-level variables as metavariables. This also means you can only construct closed terms, which
is what we want.
-}

{- Note [Metavar map functions]
These functions are a little complicated: essentially, we need to reify the whole substitution map at
compile time. Sadly, TH isn't clever enough to do this automatically, so we manually create
the list of expressions, lift it to a quoted list, and then zip it back together with the
automatically lifted list of source expressions.

Also, although they're largely identical, we have two versions so we can put
explicit type annotations in the generated code, which makes the type errors if you get
things wrong much better.
-}

substs :: [BSL.ByteString] -> Q Exp
substs fvsL = let substFun n = [| $(varE (mkName (bsToStr n)))|] in listE $ fmap substFun fvsL

-- See note [Metavar map functions]
-- | Get a quotation of a map between names and Haskell variable references to terms using the
-- name as the variable name.
metavarMapTerm :: Set.Set (Name a) -> Q Exp
metavarMapTerm ftvs = let ftvsL = nameString <$> toList ftvs in
    [|
        let
            subs :: [Quote (Term TyName Name ())]
            subs = $(substs ftvsL)
            qm :: Quote (Map.Map BSL.ByteString (Term TyName Name ()))
            qm = do
                quoted <- sequence subs
                pure $ Map.fromList $ zip ftvsL quoted
        in qm
    |]

-- See note [Metavar map functions]
-- | Get a quotation of a map between type names and Haskell variable references to types using the
-- type name as the variable name.
metavarMapType :: Set.Set (TyName a) -> Q Exp
metavarMapType ftvs = let ftvsL = nameString . unTyName <$> toList ftvs in
    [|
        let
          subs :: [Quote (Type TyName ())]
          subs = $(substs ftvsL)
          qm :: Quote (Map.Map BSL.ByteString (Type TyName ()))
          qm = do
              quoted <- sequence subs
              pure $ Map.fromList $ zip ftvsL quoted
        in qm
    |]

metavarSubstType ::
  Type TyName () ->
  Map.Map BSL.ByteString (Type TyName ()) ->
  Type TyName ()
metavarSubstType ty tyMetavars = substTy
                        (\n -> Map.lookup (nameString $ unTyName n) tyMetavars)
                        ty

metavarSubstTerm ::
  Term TyName Name () ->
  Map.Map BSL.ByteString (Type TyName ()) ->
  Map.Map BSL.ByteString (Term TyName Name ()) ->
  Term TyName Name ()
metavarSubstTerm t tyMetavars termMetavars = substTerm
                        (\n -> Map.lookup (nameString $ unTyName n) tyMetavars)
                        (\n -> Map.lookup (nameString n) termMetavars)
                        t

-- | Runs a 'QuoteT' in the 'Q' context. Note that this uses 'runQuoteT', so does note preserve freshness.
eval :: QuoteT (Except ParseError) a -> Q a
eval c = case runExcept $ runQuoteT c of
    Left e  -> fail $ show e
    Right p -> pure p

unsafeDropErrors :: Except e a -> a
unsafeDropErrors e = case runExcept e of
    Right r -> r
    Left _  -> error "Impossible!"

{-- Note [Parsing and TH stages]
We have a bit of a dilemma with the staging and parsing of PLC. We need the list of metavars at compile time
so we can wire up the Haskell variable references, but we won't know the real variable names until runtime
(since we're running things in 'Quote'!).

The solution is kind of hacky, but works nicely: the linkage to metavar is done only by *name*, which does *not*
include the unique tag. So we can parse the quasiquote at compile time to get the metavars, and then *again*
at runtime to get the real program, and still be able to wire things up (since we're going to look for free vars at
runtime by name, ignoring uniques).

The runtime parse also assumes there will be no parse errors, since we've already checked, and there is nowhere
to put them.

Finally, we need to drop the lexer position annotations, since they're not terribly useful.
-}

compileTerm :: String -> Q Exp
compileTerm s = do
    compileTimeT <- eval $ parseTerm $ strToBs s
    let
        tyMetavars = metavarMapType (ftvTerm compileTimeT)
        termMetavars = metavarMapTerm (fvTerm compileTimeT)
    [|
        let
            quoted :: Quote (Term TyName Name ())
            quoted = do
                -- See note [Parsing and TH stages]
                runtimeT <- (fmap discardAnnsTerm . mapInner (Identity . unsafeDropErrors) . parseTerm . strToBs) s
                metavarSubstTerm runtimeT <$> $(tyMetavars) <*> $(termMetavars)
        in quoted
     |]

compileType :: String -> Q Exp
compileType s = do
    compileTimeTy <- eval $ parseType $ strToBs s
    let
        tyMetavars = metavarMapType (ftvTy compileTimeTy)
    [|
        let
            quoted :: Quote (Type TyName ())
            quoted = do
                -- See note [Parsing and TH stages]
                runtimeTy <- (fmap discardAnnsTy . mapInner (Identity . unsafeDropErrors) . parseType . strToBs) s
                metavarSubstType runtimeTy <$> $(tyMetavars)
          in quoted
      |]

compileProgram :: String -> Q Exp
compileProgram s = do
    (Program _ _ compileTimeT) <- eval $ parseProgram $ strToBs s
    let
        tyMetavars = metavarMapType (ftvTerm compileTimeT)
        termMetavars= metavarMapTerm (fvTerm compileTimeT)
    [|
        let
            quoted :: Quote (Program TyName Name ())
            quoted = do
                -- See note [Parsing and TH stages]
                (Program a v runtimeT) <- (fmap discardAnnsTerm . mapInner (Identity . unsafeDropErrors) . parseProgram . strToBs) s
                Program a v . metavarSubstTerm runtimeT <$> $(tyMetavars) <*> $(termMetavars)
        in quoted
     |]

-- | A quasiquoter for creating Plutus Core types.
plcType :: QuasiQuoter
plcType = QuasiQuoter {
    quoteExp = compileType,
    quoteDec = fail "Not implemented",
    quotePat = fail "Not implemented",
    quoteType = fail "Not implemented"
}

-- | A quasiquoter for creating Plutus Core terms.
plcTerm :: QuasiQuoter
plcTerm = QuasiQuoter {
    quoteExp = compileTerm,
    quoteDec = fail "Not implemented",
    quotePat = fail "Not implemented",
    quoteType = fail "Not implemented"
 }

-- | A quasiquoter for creating Plutus Core programs.
plcProgram :: QuasiQuoter
plcProgram = QuasiQuoter {
    quoteExp = compileProgram,
    quoteDec = fail "Not implemented",
    quotePat = fail "Not implemented",
    quoteType = fail "Not implemented"
}
