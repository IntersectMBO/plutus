"""Untimed counters. These are deliberately absent from benchmark binaries."""

def instrument_function(s, name, counter):
    start = s.index(name + ' e = case e of') if name in ['sealM', 'pinM'] else s.index(name + ' x e = case e of')
    end = s.index('{-# INLINE ' + name + ' #-}', start)
    first, body = s[start:end].rstrip().split('\n', 1)
    replacement = first.replace('= case e of', '= do') + f'\n  bumpStats {counter} 1\n  case e of\n'
    replacement += '\n'.join('  '+line for line in body.splitlines()) + '\n'
    return s[:start] + replacement + s[end:]


def instrument(env, internal):
    if 'import Data.Primitive.PrimArray\n' not in env:
        env = env.replace('import Data.Primitive.SmallArray',
            'import Data.Primitive.PrimArray\nimport Data.Primitive.SmallArray')
    env = instrument_function(env, 'consM', 0)
    if 'sealM ::' in env:
        env = instrument_function(env, 'sealM', 4)
        env = instrument_function(env, 'pinM', 5)
    lines = []
    for line in env.splitlines():
        indent = line[:len(line)-len(line.lstrip())]
        if '<- newSmallArray' in line:
            lines.append(indent+'bumpStats 1 1')
        if line.lstrip().startswith('copySmallMutableArray '):
            lines.extend([indent+'bumpStats 2 1', indent+'bumpStats 3 n'])
        lines.append(line)
    env = '\n'.join(lines)+'\n'+'''
-- extensions, buffers, copies, copied slots, seals, borrows, erased closures
statsCounters :: MutablePrimArray RealWorld Int
statsCounters = unsafePerformIO $ do
  a <- newPrimArray 7
  setPrimArray a 0 7 0
  pure a
{-# NOINLINE statsCounters #-}

bumpStats :: Int -> Int -> IO ()
bumpStats i n = do
  old <- readPrimArray statsCounters i
  writePrimArray statsCounters i (old+n)

resetStats :: IO ()
resetStats = setPrimArray statsCounters 0 7 0

getStats :: IO [Int]
getStats = mapM (readPrimArray statsCounters) [0..6]
'''
    internal = internal.replace('      computeCek (FrameAwaitUncapturedArg ',
        '      CekM $ unsafeIOToST $ Env.bumpStats 6 1\n      computeCek (FrameAwaitUncapturedArg ')
    internal = internal.replace('      stepAndMaybeSpend BDelay\n      computeCek ctx env body',
        '      stepAndMaybeSpend BDelay\n      CekM $ unsafeIOToST $ Env.bumpStats 6 1\n      computeCek ctx env body')
    internal = internal.replace('    applyUncaptured ctx env body arg = do\n',
        '    applyUncaptured ctx env body arg = do\n      CekM $ unsafeIOToST $ Env.bumpStats 6 1\n')
    return env, internal
