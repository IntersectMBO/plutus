-- | Instances of the 'KnownType' class.

{-# OPTIONS_GHC -fno-warn-orphans #-}

{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE UndecidableInstances  #-}

module Language.PlutusCore.Constant.Dynamic.Instances () where

import           Language.PlutusCore.Constant.Typed
import           Language.PlutusCore.Core
import           Language.PlutusCore.Evaluation.Machine.Exception
import           Language.PlutusCore.Evaluation.Result
import           Language.PlutusCore.MkPlc
import           Language.PlutusCore.Name
import           Language.PlutusCore.StdLib.Data.Bool
import           Language.PlutusCore.Universe

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

instance KnownType uni a => KnownType uni (EvaluationResult a) where
    toTypeAst _ = toTypeAst (Proxy @a)

    -- 'EvaluationFailure' on the Haskell side becomes 'Error' on the PLC side.
    makeKnown EvaluationFailure     = Error () $ toTypeAst (Proxy @a)
    makeKnown (EvaluationSuccess x) = makeKnown x

    -- Catching 'EvaluationFailure' here would allow *not* to short-circuit when 'readKnown' fails
    -- to read a Haskell value of type @a@. Instead, in the denotation of the builtin function
    -- the programmer would be given an explicit 'EvaluationResult' value to handle, which means
    -- that when this value is 'EvaluationFailure', a PLC 'Error' was caught.
    -- I.e. it would essentially allow to catch errors and handle them in a programmable way.
    -- We forbid this, because it complicates code and is not supported by evaluation engines anyway.
    readKnown _ _ = throwingWithCause _UnliftingError "Error catching is not supported" Nothing

instance (KnownSymbol text, KnownNat uniq, uni ~ uni') =>
            KnownType uni (OpaqueTerm uni' text uniq) where
    toTypeAst _ =
        TyVar () . TyName $
            Name ()
                (Text.pack $ symbolVal @text Proxy)
                (Unique . fromIntegral $ natVal @uniq Proxy)

    makeKnown = unOpaqueTerm

    readKnown eval = fmap OpaqueTerm . eval mempty

instance (GShow uni, GEq uni, uni `Includes` Integer) => KnownType uni Integer where
    toTypeAst _ = mkTyBuiltin @Integer ()
    makeKnown = mkConstant ()
    readKnown = unliftConstantEval mempty

instance (GShow uni, GEq uni, uni `Includes` BSL.ByteString) => KnownType uni BSL.ByteString where
    toTypeAst _ = mkTyBuiltin @BSL.ByteString ()
    makeKnown = mkConstant ()
    readKnown = unliftConstantEval mempty

-- Encode 'Char' from Haskell as @integer@ from PLC.
instance (GShow uni, GEq uni, uni `Includes` Integer) => KnownType uni Char where
    toTypeAst _ = mkTyBuiltin @Integer ()
    makeKnown = mkConstant @Integer () . fromIntegral . ord
    readKnown eval term = chr . fromIntegral @Integer <$> unliftConstantEval mempty eval term

instance (GShow uni, GEq uni, uni `Includes` String, c ~ Char) => KnownType uni [c] where
    toTypeAst _ = mkTyBuiltin @String ()
    makeKnown = mkConstant ()
    readKnown = unliftConstantEval mempty

instance (GShow uni, GEq uni, uni `Includes` Integer) => KnownType uni Bool where
    toTypeAst _ = bool

    makeKnown b = if b then true else false

    readKnown eval b = do
        let integer = mkTyBuiltin @Integer ()
            integerToTerm = mkConstant @Integer ()
            -- Encode 'Bool' from Haskell as @integer 1@ from PLC.
            term = mkIterApp () (TyInst () b integer) [integerToTerm 1, integerToTerm 0]
        i <- unliftConstantEval mempty eval term
        case i :: Integer of
            0 -> pure False
            1 -> pure True
            _ -> throwingWithCause _UnliftingError "Not an integer-encoded Bool" $ Just term
