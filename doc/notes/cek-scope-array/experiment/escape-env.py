"""Alternative ownership policy: snapshot only escaping captures."""

def snapshot_on_escape(s):
    s = s.replace('-- EXPERIMENT ONLY. The evaluator owns its active environment; continuations',
        '-- EXPERIMENT ONLY: snapshot escaping closures; reuse uncaptured tails.\n'
        '-- The evaluator owns its active environment; continuations')
    s = s.replace('  sealM result\n', '  freezeM result\n')
    start = s.index('-- All actual closures must be sealed')
    end = s.index('pinM ::', start)
    s = s[:start] + '''-- An escaping capture whose prefix is already frozen can share it. Otherwise
-- snapshot it into its own buffer, leaving the active buffer's tail reusable.
-- The captured buffer also has spare capacity so calls can reuse its tail.
sealM :: RAList a -> IO (RAList a)
sealM e = case e of
  Empty _ -> pure e
  ArrayEnv n capacity a m _ -> do
    frozen <- readPrimArray m 0
    if frozen >= n then pure e else do
      b <- newSmallArray (sizeofSmallMutableArray a) (error "uninitialized slot")
      copySmallMutableArray b 0 a 0 n
      metadata <- newMetadata
      writePrimArray metadata 0 n
      pure (ArrayEnv n capacity b metadata (-1))
{-# INLINE sealM #-}

-- Persistent API fallback, which owns a fresh buffer already.
freezeM :: RAList a -> IO (RAList a)
freezeM e = case e of
  Empty _ -> pure e
  ArrayEnv n _ _ m _ -> do
    writePrimArray m 0 n
    pure e
{-# INLINE freezeM #-}

''' + s[end:]
    return s
