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
import PlutusTx.Test.Util.Compiled (countFlatBytes)
import Prettyprinter (fill, vsep, (<+>))
import Test.Tasty (TestName)
import Test.Tasty.Extras ()
import Text.Printf (printf)
import UntypedPlutusCore qualified as UPLC

-- Value assertion tests
goldenCodeGen :: TH.Ppr a => TestName -> TH.Q a -> TH.ExpQ
goldenCodeGen name code = do
  c <- code
  [|nestedGoldenVsDoc name ".th" (pretty @String $(TH.stringE $ TH.pprint c))|]

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
