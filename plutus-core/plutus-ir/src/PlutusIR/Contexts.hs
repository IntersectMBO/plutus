{-# LANGUAGE LambdaCase #-}
-- | Datatypes representing 'contexts with holes' in Plutus IR terms.
--
-- Useful for focussing on a sub-part of a term and then reconstructing the term, but
-- with the context as a reified datatype that can be inspected and modified.
module PlutusIR.Contexts where

import PlutusIR.Core

-- | A context for an iterated term/type application, with the hole at the head of the
-- application.
data AppContext tyname name uni fun ann =
  TermAppContext (Term tyname name uni fun ann) ann (AppContext tyname name uni fun ann)
  | TypeAppContext (Type tyname uni ann) ann (AppContext tyname name uni fun ann)
  | AppContextEnd

{- | Takes a term and views it as a head plus an 'AppContext', e.g.

@
    [{ f t } u v]
    -->
    (f, [{ _ t } u v])
    ==
    f (TypeAppContext t (TermAppContext u (TermAppContext v AppContextEnd)))
@
-}
splitApplication :: Term tyname name uni fun ann
  -> (Term tyname name uni fun ann, AppContext tyname name uni fun ann)
splitApplication tm
  = go tm AppContextEnd
  where
    go (Apply ann f arg) ctx    = go f (TermAppContext arg ann ctx)
    go (TyInst ann f tyArg) ctx = go f (TypeAppContext tyArg ann ctx)
    go t ctx                    = (t, ctx)

-- | Fills in the hole in an 'AppContext', the inverse of 'splitApplication'.
fillAppContext
  :: Term tyname name uni fun ann
  -> AppContext tyname name uni fun ann
  -> Term tyname name uni fun ann
fillAppContext t = \case
  AppContextEnd                -> t
  TermAppContext arg ann ctx   -> fillAppContext (Apply ann t arg) ctx
  TypeAppContext tyArg ann ctx -> fillAppContext (TyInst ann t tyArg) ctx

dropAppContext :: Int -> AppContext tyname name uni fun a -> AppContext tyname name uni fun a
dropAppContext i ctx | i <= 0 = ctx
dropAppContext i ctx = case ctx of
  AppContextEnd           -> ctx
  TermAppContext _ _ ctx' -> dropAppContext (i-1) ctx'
  TypeAppContext _ _ ctx' -> dropAppContext (i-1) ctx'

lengthContext :: AppContext tyname name uni fun a -> Int
lengthContext = go 0
  where
    go acc = \case
      AppContextEnd          -> acc
      TermAppContext _ _ ctx -> go (acc+1) ctx
      TypeAppContext _ _ ctx -> go (acc+1) ctx

{- Note [Context splitting in a recursive pass]
When writing a recursive pass that processes the whole program, you must be
a bit cautious when using a context split. The context split may traverse
part of the program, which will _also_ be traversed by the main recursive
traversal. This can lead to quadratic runtime.

This is usually okay for something like 'splitApplication', since it is
quadratic in the longest application in the program, which is usually not
significantly long.
-}
