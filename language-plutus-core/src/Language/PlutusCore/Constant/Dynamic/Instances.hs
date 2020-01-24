-- | Instances of the 'KnownType' class.

{-# OPTIONS_GHC -fno-warn-orphans #-}

{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications  #-}

module Language.PlutusCore.Constant.Dynamic.Instances () where

import           Language.PlutusCore.Constant.Make
import           Language.PlutusCore.Constant.Typed
import           Language.PlutusCore.Core
import           Language.PlutusCore.Evaluation.Result
import           Language.PlutusCore.MkPlc
import           Language.PlutusCore.Name
import           Language.PlutusCore.Pretty
import           Language.PlutusCore.StdLib.Data.Bool

import           Control.Monad.Except
import qualified Data.ByteString.Lazy                  as BSL
import           Data.Char
import           Data.Proxy
import qualified Data.Text                             as Text
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

    -- There are two 'EvaluationResult's here: an external one (which any 'KnownType'
    -- instance has to deal with) and an internal one (specific to this particular instance).
    -- Our approach is to always return 'EvaluationSuccess' for the external 'EvaluationResult'
    -- and catch all 'EvaluationFailure's in the internal 'EvaluationResult'.
    -- This allows *not* to short-circuit when 'readKnown' fails to read a Haskell value.
    -- Instead the user gets an explicit @EvaluationResult a@ and evaluation proceeds normally.
    readKnown eval = mapDeepReflectT (fmap $ EvaluationSuccess . sequence) . readKnown eval

    prettyKnown = pretty . fmap (PrettyConfigIgnore . KnownTypeValue)

instance (KnownSymbol text, KnownNat uniq) => KnownType (OpaqueTerm text uniq) where
    toTypeAst _ =
        TyVar () . TyName $
            Name ()
                (Text.pack $ symbolVal @text Proxy)
                (Unique . fromIntegral $ natVal @uniq Proxy)

    makeKnown = unOpaqueTerm

    readKnown eval = fmap OpaqueTerm . makeRightReflectT . eval mempty

instance KnownType Integer where
    toTypeAst _ = TyBuiltin () TyInteger

    makeKnown = Constant () . makeBuiltinInt

    readKnown eval term = do
        -- 'term' is supposed to be already evaluated, but calling 'eval' is the easiest way
        -- to turn 'Error' into 'EvaluationFailure', which we later 'lift' to 'Convert'.
        res <- makeRightReflectT $ eval mempty term
        case res of
            Constant () (BuiltinInt () i) -> pure i
            _                             -> throwError "Not a builtin Integer"

instance KnownType BSL.ByteString where
    toTypeAst _ = TyBuiltin () TyByteString

    makeKnown = Constant () . makeBuiltinBS

    readKnown eval term = do
        res <- makeRightReflectT $ eval mempty term
        case res of
            Constant () (BuiltinBS () i) -> pure i
            _                            -> throwError "Not a builtin ByteString"

    prettyKnown = prettyBytes

instance KnownType [Char] where
    toTypeAst _ = TyBuiltin () TyString

    makeKnown = Constant () . makeBuiltinStr

    readKnown eval term = do
        res <- makeRightReflectT $ eval mempty term
        case res of
            Constant () (BuiltinStr () s) -> pure s
            _                             -> throwError "Not a builtin String"

instance KnownType Bool where
    toTypeAst _ = bool

    makeKnown b = if b then true else false

    readKnown eval b = do
        let int = TyBuiltin () TyInteger
            asInt = Constant () . BuiltinInt ()
            -- Encode 'Bool' from Haskell as @integer 1@ from PLC.
            term = mkIterApp () (TyInst () b int) [asInt 1, asInt 0]
        res <- makeRightReflectT $ eval mempty term
        case res of
            Constant () (BuiltinInt () 1) -> pure True
            Constant () (BuiltinInt () 0) -> pure False
            _                             -> throwError "Not an integer-encoded Bool"

-- Encode 'Char' from Haskell as @integer@ from PLC.
instance KnownType Char where
    toTypeAst _ = TyBuiltin () TyInteger

    makeKnown = Constant () . makeBuiltinInt . fromIntegral . ord

    readKnown eval term = do
        res <- makeRightReflectT $ eval mempty term
        case res of
            Constant () (BuiltinInt () int) -> pure . chr $ fromIntegral int
            _                               -> throwError "Not an integer-encoded Char"
