-- | Instances of the 'KnownType' class.

{-# OPTIONS_GHC -fno-warn-orphans #-}

{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications  #-}

module Language.PlutusCore.Constant.Dynamic.Instances () where

import           Language.PlutusCore.Constant.Make
import           Language.PlutusCore.Constant.Typed
import           Language.PlutusCore.Core
import           Language.PlutusCore.Evaluation.Machine.Exception
import           Language.PlutusCore.Evaluation.Result
import           Language.PlutusCore.MkPlc
import           Language.PlutusCore.Name
import           Language.PlutusCore.Pretty
import           Language.PlutusCore.StdLib.Data.Bool

import qualified Data.ByteString.Lazy                             as BSL
import           Data.Char
import           Data.Proxy
import qualified Data.Text                                        as Text
import           GHC.TypeLits

{- Note [Sequencing]
WARNING: it is not allowed to call 'eval' or @readKnown eval@ over a term that already
was 'eval'ed. It may be temptive to preevaluate to WHNF some term if you later need to evaluate
its several instantiations, but it is forbidden to do so. The reason for this restriction is that
'eval' encapsulates its internal state and the state gets updated during evaluation, so if you
try to call 'eval' over something that already was 'eval'ed, that second 'eval' won't have the
updated state that the first 'eval' finished with. This may cause all kinds of weird error messages,
for example, an error message saying that there is a free variable and evaluation cannot proceed.
-}

instance KnownType a => KnownType (EvaluationResult a) where
    toTypeAst _ = toTypeAst @a Proxy

    -- 'EvaluationFailure' on the Haskell side becomes 'Error' on the PLC side.
    makeKnown EvaluationFailure     = Error () $ toTypeAst @a Proxy
    makeKnown (EvaluationSuccess x) = makeKnown x

    -- Catching 'EvaluationFailure' here would allow *not* to short-circuit when 'readKnown' fails
    -- to read a Haskell value of type @a@. Instead, in the denotation of the builtin function
    -- the programmer would be given an explicit 'EvaluationResult' value to handle, which means
    -- that when this value is 'EvaluationFailure', a PLC 'Error' was caught.
    -- I.e. it would essentially allow to catch errors and handle them in a programmable way.
    -- We forbid this, because it complicates code and is not supported by evaluation engines anyway.
    readKnown _ _ = throwingWithCause _UnliftingError "Catching errors is not supported" Nothing

    prettyKnown = pretty . fmap (PrettyConfigIgnore . KnownTypeValue)

instance (KnownSymbol text, KnownNat uniq) => KnownType (OpaqueTerm text uniq) where
    toTypeAst _ =
        TyVar () . TyName $
            Name ()
                (Text.pack $ symbolVal @text Proxy)
                (Unique . fromIntegral $ natVal @uniq Proxy)

    makeKnown = unOpaqueTerm

    readKnown eval = fmap OpaqueTerm . eval mempty

instance KnownType Integer where
    toTypeAst _ = TyBuiltin () TyInteger

    makeKnown = Constant () . makeBuiltinInt

    readKnown eval term = do
        -- 'term' is supposed to be already evaluated, but calling 'eval' is the easiest way
        -- to turn 'Error' into 'EvaluationFailure', which we later 'lift' to 'Convert'.
        res <- eval mempty term
        case res of
            Constant () (BuiltinInt () i) -> pure i
            _                             ->
                throwingWithCause _UnliftingError "Not a builtin Integer" $ Just term

instance KnownType BSL.ByteString where
    toTypeAst _ = TyBuiltin () TyByteString

    makeKnown = Constant () . makeBuiltinBS

    readKnown eval term = do
        res <- eval mempty term
        case res of
            Constant () (BuiltinBS () i) -> pure i
            _                            ->
                throwingWithCause _UnliftingError "Not a builtin ByteString" $ Just term

    prettyKnown = prettyBytes

instance KnownType [Char] where
    toTypeAst _ = TyBuiltin () TyString

    makeKnown = Constant () . makeBuiltinStr

    readKnown eval term = do
        res <- eval mempty term
        case res of
            Constant () (BuiltinStr () s) -> pure s
            _                             ->
                throwingWithCause _UnliftingError "Not a builtin String" $ Just term

instance KnownType Bool where
    toTypeAst _ = bool

    makeKnown b = if b then true else false

    readKnown eval b = do
        let int = TyBuiltin () TyInteger
            asInt = Constant () . BuiltinInt ()
            -- Encode 'Bool' from Haskell as @integer 1@ from PLC.
            term = mkIterApp () (TyInst () b int) [asInt 1, asInt 0]
        res <- eval mempty term
        case res of
            Constant () (BuiltinInt () 1) -> pure True
            Constant () (BuiltinInt () 0) -> pure False
            _                             ->
                throwingWithCause _UnliftingError "Not an integer-encoded Bool" $ Just term

-- Encode 'Char' from Haskell as @integer@ from PLC.
instance KnownType Char where
    toTypeAst _ = TyBuiltin () TyInteger

    makeKnown = Constant () . makeBuiltinInt . fromIntegral . ord

    readKnown eval term = do
        res <- eval mempty term
        case res of
            Constant () (BuiltinInt () int) -> pure . chr $ fromIntegral int
            _                               ->
                throwingWithCause _UnliftingError "Not an integer-encoded Char" $ Just term
