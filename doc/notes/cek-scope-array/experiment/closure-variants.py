"""Source transforms for closure erasure and temporary environment borrowing."""

def replace_once(s, old, new):
    assert s.count(old) == 1, old
    return s.replace(old, new)


def transform(s, reuse, erased, contextual=False):
    if reuse:
        s = replace_once(s, '      returnCek ctx (VLamAbs name body env)',
            '      captured <- CekM $ unsafeIOToST $ Env.sealM env\n'
            '      returnCek ctx (VLamAbs name body captured)')
        s = replace_once(s, '      returnCek ctx (VDelay body env)',
            '      captured <- CekM $ unsafeIOToST $ Env.sealM env\n'
            '      returnCek ctx (VDelay body captured)')
        s = replace_once(s, '      computeCek (FrameAwaitFunTerm env arg ctx) env fun',
            '      saved <- CekM $ unsafeIOToST $ Env.pinM env\n'
            '      computeCek (FrameAwaitFunTerm saved arg ctx) env fun')
        s = replace_once(s, '    returnCek (FrameAwaitFunTerm argVarEnv arg ctx) fun =\n'
            '      computeCek (FrameAwaitArg fun ctx) argVarEnv arg',
            '    returnCek (FrameAwaitFunTerm saved arg ctx) fun = do\n'
            '      argVarEnv <- CekM $ unsafeIOToST $ Env.unpinM saved\n'
            '      computeCek (FrameAwaitArg fun ctx) argVarEnv arg')
        s = replace_once(s,
            '        (t : rest) -> computeCek (FrameConstr env i rest NilStack ctx) env t',
            '        (t : rest) -> do\n'
            '          saved <- CekM $ unsafeIOToST $ Env.pinM env\n'
            '          computeCek (FrameConstr saved i rest NilStack ctx) env t')
        s = replace_once(s, '        [] ->\n          let go acc NilStack = acc',
            '        [] -> do\n'
            '          _ <- CekM $ unsafeIOToST $ Env.unpinM env\n'
            '          let go acc NilStack = acc')
        s = replace_once(s, '           in returnCek ctx $ VConstr',
            '          returnCek ctx $ VConstr')
        s = replace_once(s, '      computeCek (FrameCases env cs ctx) env scrut',
            '      saved <- CekM $ unsafeIOToST $ Env.pinM env\n'
            '      computeCek (FrameCases saved cs ctx) env scrut')
        start = s.index('    returnCek (FrameCases env cs ctx) e = case e of')
        end = s.index('\n\n    -- \\| @force@', start)
        body = s[start:end].split('\n', 1)[1]
        s = s[:start] + ('    returnCek (FrameCases saved cs ctx) e = do\n'
            '      env <- CekM $ unsafeIOToST $ Env.unpinM saved\n'
            '      case e of\n' + '\n'.join('  '+line for line in body.splitlines())) + s[end:]
        s = replace_once(s, '      computeCek ctx (Env.cons arg env) body',
            '      do\n'
            '        extended <- CekM $ unsafeIOToST $ Env.consM arg env\n'
            '        computeCek ctx extended body')
        s = replace_once(s,
            '    lookupVarName varName@(NamedDeBruijn _ varIx) varEnv =\n'
            '      Env.contIndexOne\n'
            '        (throwErrorWithCause (StructuralError OpenTermEvaluatedMachineError) $ Var () varName)\n'
            '        pure\n'
            '        varEnv\n'
            '        (coerce varIx)',
            '    lookupVarName varName@(NamedDeBruijn _ varIx) varEnv = do\n'
            '      found <- CekM $ unsafeIOToST $ Env.indexOneM varEnv (coerce varIx)\n'
            '      case found of\n'
            '        Nothing -> throwErrorWithCause (StructuralError OpenTermEvaluatedMachineError) $ Var () varName\n'
            '        Just !val -> pure val')
    if erased:
        s = replace_once(s, '  | NoFrame',
            '  | FrameAwaitUncapturedArg !(CekValEnv uni fun ann) !(NTerm uni fun ann) !(Context uni fun ann)\n'
            '  | NoFrame')
        immediate = ('    -- The function/delay cannot escape these syntactic uses. Keep all\n'
            '    -- original step charges, including their order and slippage checks.\n'
            '    computeCek !ctx !env (Apply _ (LamAbs _ _ body) arg) = do\n'
            '      stepAndMaybeSpend BApply\n'
            '      stepAndMaybeSpend BLamAbs\n')
        immediate += ('      saved <- CekM $ unsafeIOToST $ Env.pinM env\n' if reuse
                      else '      let saved = env\n')
        immediate += ('      computeCek (FrameAwaitUncapturedArg saved body ctx) env arg\n'
            '    computeCek !ctx !env (Force _ (Delay _ body)) = do\n'
            '      stepAndMaybeSpend BForce\n'
            '      stepAndMaybeSpend BDelay\n'
            '      computeCek ctx env body\n')
        s = replace_once(s, '    computeCek !ctx !env (Var _ varName) = do',
            immediate + '    computeCek !ctx !env (Var _ varName) = do')
        ret = '    returnCek (FrameAwaitUncapturedArg saved body ctx) arg =\n'
        if reuse:
            ret += ('      do\n'
                '        env <- CekM $ unsafeIOToST $ Env.unpinM saved\n'
                '        extended <- CekM $ unsafeIOToST $ Env.consM arg env\n'
                '        computeCek ctx extended body\n')
        else:
            ret += '      computeCek ctx (Env.cons arg saved) body\n'
        s = replace_once(s, '    returnCek NoFrame val = do', ret+'    returnCek NoFrame val = do')
    if contextual:
        # The continuation proves immediate consumption even when the closure
        # comes out of a force, case, or a multi-argument function application.
        cases = ('    computeCek (FrameAwaitFunTerm saved arg ctx) !env (LamAbs _ _ body) = do\n'
            '      stepAndMaybeSpend BLamAbs\n')
        if reuse:
            cases += ('      argEnv <- CekM $ unsafeIOToST $ Env.unpinM saved\n'
                '      borrowed <- CekM $ unsafeIOToST $ Env.pinM env\n')
        else:
            cases += '      let argEnv = saved\n          borrowed = env\n'
        cases += ('      computeCek (FrameAwaitUncapturedArg borrowed body ctx) argEnv arg\n'
            '    computeCek (FrameAwaitFunConN args ctx) !env (LamAbs _ _ body) = do\n'
            '      stepAndMaybeSpend BLamAbs\n'
            '      case args of\n'
            '        SpineLast arg -> applyUncaptured ctx env body (VCon arg)\n'
            '        SpineCons arg rest -> applyUncaptured (FrameAwaitFunConN rest ctx) env body (VCon arg)\n'
            '    computeCek (FrameAwaitFunValueN args ctx) !env (LamAbs _ _ body) = do\n'
            '      stepAndMaybeSpend BLamAbs\n'
            '      case args of\n'
            '        LastStackNonEmpty arg -> applyUncaptured ctx env body arg\n'
            '        ConsStackNonEmpty arg rest -> applyUncaptured (FrameAwaitFunValueN rest ctx) env body arg\n'
            '    computeCek (FrameForce ctx) !env (Delay _ body) = do\n'
            '      stepAndMaybeSpend BDelay\n'
            '      computeCek ctx env body\n')
        s = replace_once(s, '    computeCek !ctx !env (LamAbs _ name body) = do',
            cases + '    computeCek !ctx !env (LamAbs _ name body) = do')
        helper = ('    applyUncaptured :: Context uni fun ann -> CekValEnv uni fun ann\n'
            '      -> NTerm uni fun ann -> CekValue uni fun ann -> CekM uni fun s (DischargeResult uni fun)\n')
        if reuse:
            helper += ('    applyUncaptured ctx env body arg = do\n'
                '      extended <- CekM $ unsafeIOToST $ Env.consM arg env\n'
                '      computeCek ctx extended body\n')
        else:
            helper += ('    applyUncaptured ctx env body arg =\n'
                '      computeCek ctx (Env.cons arg env) body\n')
        s = replace_once(s, '    forceEvaluate\n', helper+'\n    forceEvaluate\n')
    return s
