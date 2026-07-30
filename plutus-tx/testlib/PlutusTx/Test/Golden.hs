{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}

module PlutusTx.Test.Golden
  ( -- * TH CodGen
    goldenCodeGen
  , goldenCodeGenNormalized

    -- * Compilation testing
  , goldenPir
  , goldenPirReadable
  , goldenPirReadableU
  , goldenPirBy
  , goldenTPlc
  , goldenUPlc
  , goldenUPlcReadable
  , goldenBudget
  , goldenAstSize

    -- * Golden evaluation testing
  , goldenEvalCek
  , goldenEvalCekCatch
  , goldenEvalCekCatchBudget
  , goldenEvalCekLog

    -- * Combined testing
  , goldenBundle
  , goldenBundle'

    -- * Pretty-printing
  , prettyBudget
  , prettyCodeSize
  ) where

import Prelude

import Control.Lens (Field1 (_1), view)
import Control.Monad.Except (runExceptT)
import Data.Char (isAlphaNum, isDigit)
import Data.List qualified as List
import Data.SatInt (fromSatInt)
import Data.Text (Text)
import Language.Haskell.TH qualified as TH
import PlutusCore qualified as PLC
import PlutusCore.Evaluation.Machine.ExBudget qualified as PLC
import PlutusCore.Evaluation.Machine.ExMemory (ExCPU (..), ExMemory (..))
import PlutusCore.Flat (Flat)
import PlutusCore.Pretty
  ( Doc
  , Pretty (pretty)
  , PrettyBy (prettyBy)
  , PrettyConfigClassic
  , PrettyConfigName
  , PrettyUni
  , Render (render)
  , prettyClassicSimple
  , prettyPlcClassicSimple
  , prettyReadable
  , prettyReadableSimple
  )
import PlutusCore.Test
  ( TestNested
  , ToUPlc (..)
  , goldenAstSize
  , goldenTPlc
  , goldenUPlc
  , goldenUPlcReadable
  , nestedGoldenVsDoc
  , nestedGoldenVsDocM
  , ppCatch
  , rethrow
  , runUPlcBudget
  )
import PlutusIR.Core.Type (progTerm)
import PlutusIR.Test ()
import PlutusTx.Code (CompiledCode, CompiledCodeIn (..), countAstNodes, getPir, getPirNoAnn)
import PlutusTx.Test.Orphans ()
import PlutusTx.Test.Run.Uplc (runPlcCek, runPlcCekBudget, runPlcCekTrace)
import PlutusTx.Test.THPretty (pprintDecs)
import PlutusTx.Test.Util.Compiled (countFlatBytes)
import Prettyprinter (fill, vsep, (<+>))
import Test.Tasty (TestName)
import Test.Tasty.Extras ()
import Text.Printf (printf)
import UntypedPlutusCore qualified as UPLC

{- Note [Stripping TH-generated unique suffixes in golden tests]
Template Haskell's 'newName' generates globally unique names by appending
large numeric suffixes (e.g., @TxOutRef_6989586621680002620@). Types defined
via 'PlutusTx.asData' use 'newName' for their internal constructor names,
so when 'deriveEq' (or similar TH derivations) reify these types, the
generated code includes these non-deterministic suffixes.

The suffixes change across compilations, making golden tests fragile --
every recompilation produces a diff even though the generated logic is
identical. We strip suffixes of 7+ digits at word boundaries to normalize
the output. Short suffixes like @_0@ or @_1@ (from local 'newName' calls
in deriveEq) are stable and left intact.
-}

-- Value assertion tests

-- | Golden test for TH-generated code, with exact output (no normalization).
goldenCodeGen :: TestName -> TH.Q [TH.Dec] -> TH.ExpQ
goldenCodeGen name code = do
  decs <- code
  [|nestedGoldenVsDoc name ".th" (pretty @String $(TH.stringE $ pprintDecs decs))|]

{-| Like 'goldenCodeGen' but strips TH-generated unique name suffixes
to produce deterministic output.
See Note [Stripping TH-generated unique suffixes in golden tests] -}
goldenCodeGenNormalized :: TestName -> TH.Q [TH.Dec] -> TH.ExpQ
goldenCodeGenNormalized name code = do
  decs <- code
  [|nestedGoldenVsDoc name ".th" (pretty @String $(TH.stringE $ stripTHSuffixes $ pprintDecs decs))|]

-- | See Note [Stripping TH-generated unique suffixes in golden tests]
stripTHSuffixes :: String -> String
stripTHSuffixes [] = []
stripTHSuffixes ('_' : rest)
  | (digits, remaining) <- span isDigit rest
  , length digits >= 7
  , atWordBoundary remaining =
      stripTHSuffixes remaining
stripTHSuffixes (c : cs) = c : stripTHSuffixes cs

atWordBoundary :: String -> Bool
atWordBoundary [] = True
atWordBoundary (c : _) = not (isAlphaNum c) && c /= '_' && c /= '\''

goldenBudget :: TestName -> CompiledCode a -> TestNested
goldenBudget name compiledCode = do
  nestedGoldenVsDocM name ".budget" $ ppCatch $ do
    budget <- runUPlcBudget [compiledCode]
    pure $
      render @Text $
        vsep
          [ prettyBudget budget
          , prettyCodeSize compiledCode
          ]

goldenBundle
  :: TestName
  -> CompiledCodeIn UPLC.DefaultUni UPLC.DefaultFun a
  -> CompiledCodeIn UPLC.DefaultUni UPLC.DefaultFun b
  -> TestNested
goldenBundle name x y = do
  goldenPirReadable name x
  goldenUPlcReadable name x
  goldenEvalCekCatchBudget name y

goldenBundle'
  :: TestName
  -> CompiledCodeIn UPLC.DefaultUni UPLC.DefaultFun a
  -> TestNested
goldenBundle' name x = goldenBundle name x x

-- | Does not print uniques.
goldenPir
  :: (PrettyUni uni, Pretty fun, uni `PLC.Everywhere` Flat, Flat fun)
  => TestName
  -> CompiledCodeIn uni fun a
  -> TestNested
goldenPir name value =
  nestedGoldenVsDoc name ".pir"
    . maybe
      "PIR not found in CompiledCode"
      (prettyClassicSimple . view progTerm)
    $ getPirNoAnn value

-- | Does not print uniques.
goldenPirReadable
  :: (PrettyUni uni, Pretty fun, uni `PLC.Everywhere` Flat, Flat fun)
  => TestName
  -> CompiledCodeIn uni fun a
  -> TestNested
goldenPirReadable name value =
  nestedGoldenVsDoc name ".pir"
    . maybe
      "PIR not found in CompiledCode"
      (prettyReadableSimple . view progTerm)
    $ getPirNoAnn value

{-| Prints uniques. This should be used sparingly: a simple change to a script or a
compiler pass may change all uniques, making it difficult to see the actual
change if all uniques are printed. It is nonetheless useful sometimes. -}
goldenPirReadableU
  :: (PrettyUni uni, Pretty fun, uni `PLC.Everywhere` Flat, Flat fun)
  => TestName
  -> CompiledCodeIn uni fun a
  -> TestNested
goldenPirReadableU name value =
  nestedGoldenVsDoc name ".pir"
    . maybe "PIR not found in CompiledCode" (prettyReadable . view progTerm)
    $ getPirNoAnn value

goldenPirBy
  :: (PrettyUni uni, Pretty fun, uni `PLC.Everywhere` Flat, Flat fun)
  => PrettyConfigClassic PrettyConfigName
  -> TestName
  -> CompiledCodeIn uni fun a
  -> TestNested
goldenPirBy config name value =
  nestedGoldenVsDoc name ".pir" $ prettyBy config $ getPir value

goldenEvalCek
  :: ToUPlc a PLC.DefaultUni PLC.DefaultFun
  => TestName
  -> a
  -> TestNested
goldenEvalCek name value =
  nestedGoldenVsDocM name ".eval" $
    prettyPlcClassicSimple <$> rethrow (runPlcCek value)

goldenEvalCekCatch
  :: ToUPlc a PLC.DefaultUni PLC.DefaultFun
  => TestName -> a -> TestNested
goldenEvalCekCatch name value =
  nestedGoldenVsDocM name ".eval" $
    either (pretty . show) prettyPlcClassicSimple
      <$> runExceptT (runPlcCek value)

goldenEvalCekCatchBudget :: TestName -> CompiledCode a -> TestNested
goldenEvalCekCatchBudget name compiledCode =
  nestedGoldenVsDocM name ".eval" $ ppCatch $ do
    (termRes, budget) <- runPlcCekBudget compiledCode
    let contents =
          vsep
            [ prettyBudget budget
            , prettyCodeSize compiledCode
            , mempty
            , prettyPlcClassicSimple termRes
            ]
    pure (render @Text contents)

goldenEvalCekLog
  :: ToUPlc a PLC.DefaultUni PLC.DefaultFun
  => TestName -> a -> TestNested
goldenEvalCekLog name value =
  nestedGoldenVsDocM name ".eval" $
    prettyPlcClassicSimple . view _1 <$> rethrow (runPlcCekTrace value)

-- | Pretty-print an Execution Budget
prettyBudget :: PLC.ExBudget -> Doc ann
prettyBudget (PLC.ExBudget (ExCPU cpu) (ExMemory mem)) =
  vsep
    [ fill 10 "CPU:" <+> prettyIntRightAligned (fromSatInt @Int cpu)
    , fill 10 "Memory:" <+> prettyIntRightAligned (fromSatInt @Int mem)
    ]

{-| Pretty-print compiled code size

Given a UPLC program, there are two quantification of "size": AST Size and Flat Size.
AST Size measures AST nodes of the given UPLC program. Flat Size measures the number
of bytes when the given program serialized into bytestring using binary flat encoding format.

Cost of storing smart contract onchain is partially determined by the Flat size. So it
is useful to have Flat size measurement in case we adopt new or introduce optimizations
to the flat encoding format. -}
prettyCodeSize :: CompiledCodeIn PLC.DefaultUni PLC.DefaultFun a -> Doc ann
prettyCodeSize compiledCode =
  vsep
    [ fill 10 "AST Size:" <+> prettyIntRightAligned astSize
    , fill 10 "Flat Size:" <+> prettyIntRightAligned flatSize
    ]
  where
    astSize = countAstNodes compiledCode
    flatSize = countFlatBytes compiledCode

prettyIntRightAligned :: Integral i => i -> Doc ann
prettyIntRightAligned =
  pretty @String
    . printf "%19s"
    . reverse
    . List.intercalate "_"
    . chunksOf 3
    . reverse
    . show @Integer
    . fromIntegral
  where
    chunksOf _ [] = []
    chunksOf n xs = take n xs : chunksOf n (drop n xs)
