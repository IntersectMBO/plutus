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

import           Language.PlutusCore.Interpreter.CekMachine

import           Language.PlutusCore.Builtin.Call
import           Language.PlutusCore.Builtin.Common

import           Data.Char
import           Data.Functor                               (void)
import           Data.Functor.Compose                       (Compose (..))
import           Data.Proxy
import qualified Data.Text.Prettyprint.Doc                  as Doc
import           System.IO.Unsafe                           (unsafePerformIO)

import           Control.Exception                          (evaluate)

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

    readDynamicBuiltin _ (Constant () (BuiltinInt () 4 int)) = Just . chr $ fromIntegral int
    readDynamicBuiltin _ _                                   = Nothing

instance PrettyDynamic Char

{-
         ┃     │ Type mismatch at () in term
         ┃     │   '(lam u (all a (type) (fun a a)) (builtin emit))'.
         ┃     │ Expected type
         ┃     │   '(fun (all a (type) (fun a a)) (fun [(lam a (type) (fix list (all r (type) (fun r (fun (fun a (fun list r)) r))))) [(con integer) (con 4)]] (all a (type) (fun a a))))',
         ┃     │ found type
         ┃     │   '(fun (all a (type) (fun a a)) (fun (fix list (all r (type) (fun r (fun (fun [(con integer) (con 4)] (fun list r)) r)))) (all a (type) (fun a a))))'
-}

instance KnownDynamicBuiltinType dyn => KnownDynamicBuiltinType [dyn] where
    getTypeEncoding proxyListDyn =
        fmap (_recursiveType . holedToRecursive) $
            holedTyApp <$> getBuiltinList <*> getTypeEncoding (argumentProxy proxyListDyn)

    makeDynamicBuiltin xs = do
        mayDyns <- getCompose $ traverse (Compose . makeDynamicBuiltin) xs
        argTy <- getTypeEncoding xs  -- Here we use '[]' as a @proxy@. Don't judge me, I'm only human.
        traverse (getListToBuiltinList argTy) mayDyns

    readDynamicBuiltin eval list = withResultProxy $ \proxyListDyn -> do
        let (xs, res) =
                unsafePerformIO . withEmit $ \emit -> do
                    l <- readLn :: IO Int
                    -- withEmitTypecheckEvaluate TypedBuiltinDyn $ \emit ->
                    let dynamicEmitName = DynamicBuiltinName $ "emit" <> prettyText l
                        dynamicEmitTerm = dynamicCall dynamicEmitName
                        dynamicEmitDefinition = dynamicCallAssign TypedBuiltinDyn dynamicEmitName emit
                        env = insertDynamicBuiltinNameDefinition dynamicEmitDefinition mempty
                    -- foldList {dyn} {unit} (\(r : unit) -> emit) unitval list
                    evaluate . eval env . runQuote $ do
                        dyn      <- getTypeEncoding $ argumentProxy proxyListDyn
                        unit     <- getBuiltinUnit
                        unitval  <- getBuiltinUnitval
                        foldList <- getBuiltinFoldList
                        u <- freshName () "u"
                        return $
                            mkIterApp () (mkIterInst () foldList [dyn, unit])
                                [LamAbs () u unit dynamicEmitTerm, unitval, list]
        {-case errOrRes of
            Left err  -> error . docString $ prettyPlcClassicDebug err
            Right res ->-}
        void $ evaluationResultToMaybe res
        Just xs

instance PrettyDynamic a => PrettyDynamic [a] where
    prettyDynamic = Doc.list . map prettyDynamic

blah :: Maybe [String]
blah = runQuote (makeDynamicBuiltin ["a" :: String, "bcd", "ef"]) >>= readDynamicBuiltin evaluateCek



{-
[
  [
    {
      (abs
        a_95
        (type)
        (lam
          x_96
          a_95
          (lam
            xs_97
            [(lam a_98 (type) (fix list_99 (all r_100 (type) (fun r_100 (fun (fun a_98 (fun list_99 r_100)) r_100))))) a_95]
            (wrap
              list_101
              [(lam a_102 (type) (all r_103 (type) (fun r_103 (fun (fun a_102 (fun list_101 r_103)) r_103)))) a_95]
              (abs
                r_104
                (type)
                (lam
                  z_105
                  r_104
                  (lam
                    f_106
                    (fun a_95 (fun [(lam a_107 (type) (fix list_108 (all r_109 (type) (fun r_109 (fun (fun a_107 (fun list_108 r_109)) r_109))))) a_95] r_104))
                    [ [ f_106 x_96 ] xs_97 ]
                  )
                )
              )
            )
          )
        )
      )
      [(lam a_110 (type) (fix list_111 (all r_112 (type) (fun r_112 (fun (fun a_110 (fun list_111 r_112)) r_112))))) [(con integer) (con 4)]]
    }
    {
      (abs
        a_113
        (type)
        (wrap
          list_114
          [(lam a_115 (type) (all r_116 (type) (fun r_116 (fun (fun a_115 (fun list_114 r_116)) r_116)))) a_113]
          (abs
            r_117
            (type)
            (lam
              z_118
              r_117
              (lam
                f_119
                (fun a_113 (fun [(lam a_120 (type) (fix list_121 (all r_122 (type) (fun r_122 (fun (fun a_120 (fun list_121 r_122)) r_122))))) a_113] r_117))
                z_118
              )
            )
          )
        )
      )
      [(con integer) (con 4)]
    }
  ]
  {
    (abs
      a_123
      (type)
      (wrap
        list_124
        [(lam a_125 (type) (all r_126 (type) (fun r_126 (fun (fun a_125 (fun list_124 r_126)) r_126)))) a_123]
        (abs
          r_127
          (type)
          (lam
            z_128
            r_127
            (lam
              f_129
              (fun a_123 (fun [(lam a_130 (type) (fix list_131 (all r_132 (type) (fun r_132 (fun (fun a_130 (fun list_131 r_132)) r_132))))) a_123] r_127))
              z_128
            )
          )
        )
      )
    )
    [(lam a_133 (type) (fix list_134 (all r_135 (type) (fun r_135 (fun (fun a_133 (fun list_134 r_135)) r_135))))) [(con integer) (con 4)]]
  }
]
-}
