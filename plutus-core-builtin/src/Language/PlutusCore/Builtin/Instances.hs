-- | A dynamic built-in type test.

{-# OPTIONS_GHC -fno-warn-orphans #-}

{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes        #-}

module Language.PlutusCore.Builtin.Instances
    () where

import           Language.PlutusCore
import           Language.PlutusCore.Constant
import           Language.PlutusCore.Evaluation.Result
import           Language.PlutusCore.MkPlc
import           Language.PlutusCore.Pretty
import           Language.PlutusCore.StdLib.Data.List
import           Language.PlutusCore.StdLib.Data.Unit
import           Language.PlutusCore.StdLib.Meta
import           Language.PlutusCore.StdLib.Type

import           Language.PlutusCore.Builtin.Common

import           Data.Char
import           Data.Functor                          (void)
import           Data.Functor.Compose                  (Compose (..))
import           Data.Proxy
import qualified Data.Text.Prettyprint.Doc             as Doc
import           System.IO.Unsafe                      (unsafePerformIO)

argumentProxy :: proxy (f a) -> Proxy a
argumentProxy _ = Proxy

withResultProxy :: (Proxy dyn -> result dyn) -> result dyn
withResultProxy k = k Proxy

{- Note [Converting PLC values to Haskell values]
The first thought that comes to mind when you asked to convert a PLC value to the corresponding Haskell
value is "just match on the AST". This works nicely for simple things like 'Char's which we encode as
@integer@s, see the @KnownDynamicBuiltinType Char@ instance below.

But how to convert something more complicated like lists? A PLC list gets passed as argument to
a built-in after it gets evaluated to WHNF. We can't just match on the AST here, because after
the initial lambda it can be anything there: function applications, other built-ins, recursive data,
anything. "Well, just normalize it" -- not so fast: for one, we did not have a term normalization
procedure at the moment this note was written, for two, it's not something that can be easily done,
because you have to carefully handle uniques (we generate new terms during evaluation) and perform type
substitutions, because types must be preserved.

Besides, matching on the AST becomes really complicated: you have to ensure that a term does have
an expected semantics by looking at the term's syntax. Huge pattern matches followed by multiple
checks that variables have equal names in right places and have distinct names otherwise. Making a
mistake is absolutely trivial here. Of course, one could just omit checks and hope it'll work alright,
but eventually it'll break and debugging won't be fun at all.

So instead of dealing with syntax of terms, we deal with their semantics. Namely, we evaluate terms
using the CEK machine. For the temporary lack of ability to put values of arbitrary Haskell types into
the Plutus Core AST, we convert PLC values to Haskell values and "emit" the latter via a combination
of 'unsafePerformIO' and 'IORef'. Here is how it looks for lists, for example:

    plcListToHaskellList =
        evaluateCek anEnvironment (foldList {dyn} {unit} (\(r : unit) -> emit) unitval list)

where `emit` is a dynamic built-in name that calls 'unsafePerformIO' over a Haskell function that
appends an element to the list stored in an 'IORef'. After evaluation finishes, we read a Haskell
list from the 'IORef' (which requires another 'unsafePerformIO') and return it.
-}

-- Encode 'Char' from Haskell as @integer 4@ from PLC.
instance KnownDynamicBuiltinType Char where
    getTypeEncoding _ = return $ TyApp () (TyBuiltin () TyInteger) (TyInt () 4)

    makeDynamicBuiltin = pure . fmap (Constant ()) . makeBuiltinInt 4 . fromIntegral . ord

    readDynamicBuiltin (Constant () (BuiltinInt () 4 int)) = Just . chr $ fromIntegral int
    readDynamicBuiltin _                                   = Nothing

instance PrettyDynamic Char

instance KnownDynamicBuiltinType dyn => KnownDynamicBuiltinType [dyn] where
    getTypeEncoding proxyListDyn =
        fmap (_recursiveType . holedToRecursive) $
            holedTyApp <$> getBuiltinList <*> getTypeEncoding (argumentProxy proxyListDyn)

    makeDynamicBuiltin xs = do
        mayDyns <- getCompose $ traverse (Compose . makeDynamicBuiltin) xs
        argTy <- getTypeEncoding xs  -- Here we use '[]' as a @proxy@. Don't judge me, I'm only human.
        traverse (getListToBuiltinList argTy) mayDyns

    readDynamicBuiltin list = withResultProxy $ \proxyListDyn -> do
        let (xs, errOrRes) =
                unsafePerformIO . withEmitTypecheckEvaluate TypedBuiltinDyn $ \emit ->
                    -- foldList {dyn} {unit} (\(r : unit) -> emit) unitval list
                    runQuote $ do
                        dyn      <- getTypeEncoding $ argumentProxy proxyListDyn
                        unit     <- getBuiltinUnit
                        unitval  <- getBuiltinUnitval
                        foldList <- getBuiltinFoldList
                        u <- freshName () "u"
                        return
                            $ mkIterApp () (mkIterInst () foldList [dyn, unit])
                                [LamAbs () u unit emit, unitval, list]
        case errOrRes of
            Left err  -> error $ prettyPlcDefString err
            Right res -> void $ evaluationResultToMaybe res
        Just xs

instance PrettyDynamic a => PrettyDynamic [a] where
    prettyDynamic = Doc.list . map prettyDynamic
