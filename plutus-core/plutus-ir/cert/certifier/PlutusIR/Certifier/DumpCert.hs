{-# LANGUAGE TypeOperators #-}
module PlutusIR.Certifier.DumpCert (dumpCert) where

import PlutusCore qualified as PLC
import PlutusIR qualified as PIR
import PlutusIR.Certifier.ToCoq qualified as PIR
import PlutusIR.Compiler.Types qualified as PIR

import Control.Monad
import Text.Printf (printf)

-- | Dumps the compilation trace (all PIR ASTs in that PIR-PIR passes of the
-- compiler) to files. Per pass, it dumps a
--   - .pir.ast file, which contains the AST (ad-hoc pretty printing strategy
--     which should probably change at some point. It basically implements a
--     Show-like representation without record syntax so it easy to parse on the
--     Coq side.)
--   - .pir.meta file with additional data, such as the unconditionally
--   inlined variables of the inliner
--
-- Eventually, this should also run the Coq certifier to produce that turns the
-- dumped information into proofs of correct compilation.
dumpCert ::
    forall uni fun a.
    ( uni ~ PLC.DefaultUni
    , fun ~ PLC.DefaultFun
    ) =>
    String -> PIR.CompilationTrace uni fun a -> IO ()
dumpCert moduleName (PIR.CompilationTrace tInit prs) = do
  dumpPass 0 Nothing tInit
  forM_ (zip [1..] prs) $ \(n, (meta, t)) -> do
    dumpPass n (Just meta) t

  where
    dumpPass :: Int -> Maybe PIR.PassMeta -> PIR.Term PIR.TyName PIR.Name uni fun a -> IO ()
    dumpPass n mMeta t = do
      let baseName = printf "%03d" n ++ "_" ++ moduleName
      writeFile (baseName ++ ".pir.ast") (PIR.toCoq t)
      forM_ mMeta $ \m ->
        writeFile (baseName ++ ".pir.meta") (PIR.toCoq m)

