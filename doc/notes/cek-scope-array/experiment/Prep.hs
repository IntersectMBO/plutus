{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE LambdaCase #-}
-- The fused analysis returns Either String Int. Force the Int too: merely
-- forcing the Right constructor would leave the maximum-depth reduction lazy.
module Prep where
import Control.DeepSeq (force)
import Control.Exception (evaluate)
import Control.Monad (foldM, forM_, unless)
import PlutusCore.DeBruijn (Index (..), NamedDeBruijn (..))
import UntypedPlutusCore qualified as U
import Main qualified as B
import System.Environment (getArgs)
import GHC.Stats (getRTSStatsEnabled)

-- Carry the maximum as a strict accumulator; update it only at binders.
-- Avoid constructing a lazy maximum at every AST node.
capacityStrict :: B.Term -> Either String Int
capacityStrict = go 0 0
  where
    go !d !high = \case
      U.Var _ (NamedDeBruijn _ (Index i))
        | i > 0 && i <= fromIntegral d -> Right high
        | otherwise -> Left "free variable"
      U.LamAbs _ (NamedDeBruijn _ (Index b)) t
        | b == 0 -> go (d + 1) (max high (d + 1)) t
        | otherwise -> Left "nonzero binder"
      U.Apply _ f x -> go d high f >>= \h -> go d h x
      U.Delay _ t -> go d high t
      U.Force _ t -> go d high t
      U.Constr _ _ ts -> foldM (go d) high ts
      U.Case _ t ts -> go d high t >>= \h -> foldM (go d) h ts
      _ -> Right high
{-# NOINLINE capacityStrict #-}

main :: IO ()
main = do
  [dir, targetText] <- getArgs
  terms <- B.loadTerms dir >>= evaluate . force
  enabled <- getRTSStatsEnabled
  unless enabled (error "preparation measurements require +RTS -T")
  let target = read targetText
      depth t = case B.capacity t of
        Left e -> error e
        Right n -> n
  forM_ terms $ \(_,t) -> do
    unless (B.scope t == Right ()) (error "scope failure")
    unless (capacityStrict t == B.capacity t) (error "capacity mismatch")
  forM_ [B.var 0, B.var 1, B.lam (B.var 2), U.Constr () 0 [B.var 1],
          B.lam (B.lam B.unit)] $ \t ->
    unless (capacityStrict t == B.capacity t) (error "scope regression")
  putStrLn "name,reps,seconds,cpu_seconds,allocated_bytes"
  mapM_ (B.measure target "scope" B.scope) terms
  mapM_ (B.measure target "capacity-forced" depth) terms
  mapM_ (B.measure target "capacity-strict" (either error id . capacityStrict)) terms
