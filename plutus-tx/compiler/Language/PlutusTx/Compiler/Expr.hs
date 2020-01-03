{-# LANGUAGE ConstraintKinds   #-}
{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ViewPatterns      #-}

-- | Functions for compiling GHC Core expressions into Plutus Core terms.
module Language.PlutusTx.Compiler.Expr (compileExpr, compileExprWithDefs, compileDataConRef) where

import           PlutusPrelude                          (bsToStr)

import           Language.PlutusTx.Compiler.Binders
import           Language.PlutusTx.Compiler.Builtins
import           Language.PlutusTx.Compiler.Error
import           Language.PlutusTx.Compiler.Laziness
import           Language.PlutusTx.Compiler.Names
import           Language.PlutusTx.Compiler.Primitives
import           Language.PlutusTx.Compiler.Type
import           Language.PlutusTx.Compiler.Types
import           Language.PlutusTx.Compiler.Utils
import           Language.PlutusTx.PIRTypes

import qualified Class                                  as GHC
import qualified FV                                     as GHC
import qualified GhcPlugins                             as GHC
import qualified MkId                                   as GHC
import qualified PrelNames                              as GHC

import qualified Language.PlutusIR                      as PIR
import qualified Language.PlutusIR.Compiler.Definitions as PIR
import           Language.PlutusIR.Compiler.Names
import qualified Language.PlutusIR.MkPir                as PIR
import qualified Language.PlutusIR.Value                as PIR

import qualified Language.PlutusCore                    as PLC
import qualified Language.PlutusCore.Constant           as PLC

import           Control.Monad.Reader

import qualified Data.ByteString.Lazy                   as BSL
import           Data.List                              (elem, elemIndex)
import qualified Data.List.NonEmpty                     as NE
import qualified Data.Set                               as Set
import qualified Data.Text                              as T
import           Data.Traversable

{- Note [System FC and System FW]
Haskell uses system FC, which includes type equalities and coercions.

PLC does *not* have coercions in particular. However, PLC also does not have a nominal
type system - everything is constructed via operators on base types, so we have no
need for coercions to convert between newtypes and datatypes.
-}


-- Literals and primitives

{- Note [Literals]
GHC's literals and primitives are a bit of a pain, since they not only have a Literal
containing the actual data, but are wrapped in special functions (often ending in the magic #).

This is a pain to recognize.
-}

{- Note [unpackFoldrCString#]
This function is introduced by rewrite rules, and usually eliminated by them in concert with `build`.

However, since we often mark things as INLINABLE, we get pre-optimization Core where only the
first transformation has fired. So we need to do something with the function.

- We can't easily turn it into a normal fold expression, since we'd need to make a lambda and
  we're not in 'CoreM' so we can't make fresh names.
- We can't easily translate it to a builtin, since we don't support higher-order functions.

So we use a horrible hack and match on `build . unpackFoldrCString#` to "undo" the original rewrite
rule.
-}

{- Note [Addr#]
String literals usually have type `Addr#`. This is not very nice for us, since we certainly don't have
those.

However, they should only appear wrapped by an `unpackCString#` or similar. Except if the string literal
gets lifted out by GHC! This is no problem for our compiler, we will just compile the literal as a binding
and put in a reference... except that the binding would need to be of type `Addr#`.

So we use another horrible hack and pretend that `Addr#` is `String`, since we treat `unpackCString#` as doing nothing.
-}

compileLiteral :: Compiling m => GHC.Literal -> m PIRTerm
compileLiteral = \case
    -- Just accept any kind of number literal, we'll complain about types we don't support elsewhere
    (GHC.LitNumber _ i _) -> pure $ PIR.Constant () $ PLC.BuiltinInt () i
    GHC.MachStr bs     ->
        -- Convert the bytestring into a core expression representing the list
        -- of characters, then compile that!
        -- Note that we do *not* convert this into a PLC string, but rather a list of characters,
        -- since that is what other Haskell code will expect.
        let
            str = bsToStr (BSL.fromStrict bs)
            charExprs = fmap GHC.mkCharExpr str
            listExpr = GHC.mkListExpr GHC.charTy charExprs
        in compileExpr listExpr
    GHC.MachChar c     -> pure $ PIR.embed $ PLC.makeKnown c
    GHC.MachFloat _    -> throwPlain $ UnsupportedError "Literal float"
    GHC.MachDouble _   -> throwPlain $ UnsupportedError "Literal double"
    GHC.MachLabel {}   -> throwPlain $ UnsupportedError "Literal label"
    GHC.MachNullAddr   -> throwPlain $ UnsupportedError "Literal null"

-- | Convert a reference to a data constructor, i.e. a call to it.
compileDataConRef :: Compiling m => GHC.DataCon -> m PIRTerm
compileDataConRef dc =
    let
        tc = GHC.dataConTyCon dc
    in do
        dcs <- getDataCons tc
        constrs <- getConstructors tc

        -- TODO: this is inelegant
        index <- case elemIndex dc dcs of
            Just i  -> pure i
            Nothing -> throwPlain $ CompilationError "Data constructor not in the type constructor's list of constructors"

        pure $ constrs !! index

-- | Finds the alternative for a given data constructor in a list of alternatives. The type
-- of the overall match must also be provided.
--
-- This differs from 'GHC.findAlt' in what it does when the constructor is not matched (this can
-- happen when the match is exhaustive *in context* only, see the doc on 'GHC.Expr'). We need an
-- alternative regardless, so we make an "impossible" alternative since this case should be unreachable.
findAlt :: GHC.DataCon -> [GHC.CoreAlt] -> GHC.Type -> GHC.CoreAlt
findAlt dc alts t = case GHC.findAlt (GHC.DataAlt dc) alts of
    Just alt -> alt
    Nothing  -> (GHC.DEFAULT, [], GHC.mkImpossibleExpr t)

-- | Make the alternative for a given 'CoreAlt'.
compileAlt
    :: Compiling m
    => Bool -- ^ Whether we must delay the alternative.
    -> [GHC.Type] -- ^ The instantiated type arguments for the data constructor.
    -> GHC.CoreAlt -- ^ The 'CoreAlt' representing the branch itself.
    -> m PIRTerm
compileAlt mustDelay instArgTys (alt, vars, body) = withContextM 3 (sdToTxt $ "Creating alternative:" GHC.<+> GHC.ppr alt) $ case alt of
    GHC.LitAlt _  -> throwPlain $ UnsupportedError "Literal case"
    GHC.DEFAULT   -> do
        body' <- compileExpr body >>= maybeDelay mustDelay
        -- need to consume the args
        argTypes <- mapM compileTypeNorm instArgTys
        argNames <- forM [0..(length argTypes -1)] (\i -> safeFreshName () $ "default_arg" <> (T.pack $ show i))
        pure $ PIR.mkIterLamAbs (zipWith (PIR.VarDecl ()) argNames argTypes) body'
    -- We just package it up as a lambda bringing all the
    -- vars into scope whose body is the body of the case alternative.
    -- See Note [Iterated abstraction and application]
    -- See Note [Case expressions and laziness]
    GHC.DataAlt _ -> mkIterLamAbsScoped vars (compileExpr body >>= maybeDelay mustDelay)

-- See Note [GHC runtime errors]
isErrorId :: GHC.Id -> Bool
isErrorId ghcId = ghcId `elem` GHC.errorIds

-- See Note [Uses of Eq]
isProbablyBytestringEq :: GHC.Id -> Bool
isProbablyBytestringEq (GHC.getName -> n)
    | Just m <- GHC.nameModule_maybe n
    , GHC.moduleNameString (GHC.moduleName m) == "Data.ByteString.Internal" || GHC.moduleNameString (GHC.moduleName m) == "Data.ByteString.Lazy.Internal"
    , GHC.occNameString (GHC.nameOccName n) == "eq"
    = True
isProbablyBytestringEq _ = False

{- Note [GHC runtime errors]
GHC has a number of runtime errors for things like pattern matching failures and so on.

We just translate these directly into calls to error, throwing away any other information.

Annoyingly, unlike void, we can't mangle the type uniformly to make sure we are safe
with respect to the value restriction (see note [Value restriction]), so we just have to force
our error call and hope that it doesn't end up somewhere it shouldn't.
-}

{- Note [Uses of Eq]
Eq can pop up in some annoying places:
- Literal patterns can introduce guards that use == from Eq
- Users can just plain use it instead of our Eq

This typically then leads to things we can't compile.

So, we can try and give an error when people do this. The obvious thing to do is to give an
error if we see a method of Eq. However, this doesn't work since the methods often get
inlined before we see them, either by the simplifier pass we run on our own module, or
because the simplifier does at least gentle inlining on unfoldings from other modules
before we see them.

So we have a few special cases in addition to catch things that look like inlined Integer or
ByteString equality, since those are especially likely to come up.
-}

{- Note [At patterns]
GHC handles @-patterns by adding a variable to each case expression representing the scrutinee
of the expression.

We handle this by simply let-binding that variable outside our generated case. In the instances
where it's not used, the PIR dead-binding pass will remove it.
-}

{- Note [Default-only cases]
GHC sometimes generates case expressions where there is only a single alternative, which is a default
alternative. It can do this even if the argument is a type variable (i.e. not known to be a datatype).
What this amounts to is ensuring the expression is evaluated - hence once place this appears is bang
patterns.

We can't actually compile this as a pattern match, since we need to know the actual type to do that.
But in the case where the only alternative is a default alternative, we don't *need* to, because it
doesn't actually inspect the contents of the datatype. So we can just compile this by returning
the body of the alternative.
-}

{- Note [Coercions and newtypes]
GHC is keen to put coercions in, they're usually great for it. However, this is a pain for us, since
you can have all kinds of fancy coercions, like coercions between functions where some of the arguments
are newtypes. We don't need to support all the stuff you can do with coercions, but we do want to
support newtypes.

A previous approach was to inspect coercions to try and work out if they were coercions between a newtype
and its underlying type, and if so manually construct/deconstruct it. This had a number of disadvantages.
- It only worked on very specific cases (e.g. if the simplifier gets loose it can make more complicated
  coercions that we can't obviously deconstruct without much more work)
- It wasn't future-proof. It's likely that GHC will move in the direction of getting rid of the structure
  of coercions (see https://gitlab.haskell.org//ghc/ghc/issues/8095#note_108189), so this approach might
  well stop working in the future.

So we would like to "believe" coercions, for at least some cases. We can
do this by always treating a newtype as it's underlying type. Except - this doesn't work for recursive
newtypes (we loop!). GHC doesn't have this problem because it treats the underlying type and the
newtype as separate types that happen to have the same representation. We don't have a separate representation
so we don't have that option.

So for the moment we:
- Treat newtypes as their underlying type.
- Blackhole newtypes when we start converting them so we can bail if they're recursive.
- Always believe coercions (i.e. just treat casts as the identity).

The final point could get us into trouble with fancier uses of coercions (since we will just accept them),
but those should fail when we typecheck the PLC. And we explicitly say we don't support such things.
-}

{- Note [Unfoldings]
GHC stores the current RHS of bindings in "unfoldings". These are used for inlining, but
also generally provide the compiler's view of the RHS of a binding. They are usually available
for other modules in the same package, and can be available cross-package if GHC decides it's
a good idea or if the binding is marked INLINABLE (or if you use `-fexpose-all-unfoldings`).

We use unfoldings to get the definitions of non-locally bound names. We then hoist these into
definitions using PIR's support for definitions. This allows a relatively direct form of code
reuse - provided that the code you are reusing has unfoldings! In practice this means you may
need to scatter some INLINABLE pragmas around, but we may be able to improve this in future,
see e.g. https://gitlab.haskell.org/ghc/ghc/issues/10871.

(Since unfoldings are updated as the compiler progresses, unfoldings for bindings in other
modules are typically fully-optimized. The exception is the unfoldings for INLINABLE bindings,
which get the *pre* optimization RHS. This is so that rewrite rules can fire. In practice, this
means that we need to be okay getting either.)
-}

{- Note [Non-strict let-bindings]
Haskell is a non-strict language, PLC is a strict language. One place that can show up is in let-bindings.
In particular, a let-binding where the RHS is not value may behave differently.
e.g.
```
let e = error in if x then e else ()
```
In Haskell this is conditionally error, in PLC it is unconditionally error.

These sorts of thing can be written by the user, or generated by GHC.

We solve this by compiling such let-bindings *non-strictly*. That means we delay the body
and force all uses of it. This is a bit overenthusiastic, as it will add overhead to
effect-free let-bindings, but I don't know of an easy way to tell if an expression is pure.

Conveniently, we can just use PIR's support for non-strict let bindings to implement this.
-}

hoistExpr :: Compiling m => GHC.Var -> GHC.CoreExpr -> m PIRTerm
hoistExpr var t =
    let
        name = GHC.getName var
        lexName = LexName name
    in withContextM 1 (sdToTxt $ "Compiling definition of:" GHC.<+> GHC.ppr var) $ do
        maybeDef <- PIR.lookupTerm () lexName
        case maybeDef of
            Just term -> pure term
            Nothing -> do
                let fvs = GHC.getName <$> (GHC.fvVarList $ GHC.expr_fvs t)
                let tcs = GHC.getName <$> (GHC.nonDetEltsUniqSet $ tyConsOfExpr t)
                let allFvs = Set.fromList $ fvs ++ tcs

                var' <- compileVarFresh var
                -- See Note [Occurrences of recursive names]
                PIR.defineTerm
                    lexName
                    (PIR.Def var' (PIR.mkVar () var', PIR.Strict))
                    mempty

                t' <- compileExpr t

                -- See Note [Non-strict let-bindings]
                let nonStrict = not $ PIR.isTermValue t'
                -- We could incur a dependency on unit for a number of reasons: we delayed,
                -- or we used it for a lazy case expression. Rather than tear our hair out
                -- trying to work out whether we do depend on it, just assume that we do.
                -- This should get better when we push the laziness handling to PIR so we
                -- can trust the source-level dependencies on unit.
                let deps = Set.insert (GHC.getName GHC.unitTyCon) allFvs

                PIR.defineTerm
                    lexName
                    (PIR.Def var' (t', if nonStrict then PIR.NonStrict else PIR.Strict))
                    (Set.map LexName deps)
                pure $ PIR.mkVar () var'

-- Expressions

compileExpr :: Compiling m => GHC.CoreExpr -> m PIRTerm
compileExpr e = withContextM 2 (sdToTxt $ "Compiling expr:" GHC.<+> GHC.ppr e) $ do
    -- See Note [Scopes]
    CompileContext {ccScopes=stack} <- ask
    let top = NE.head stack
    case e of
        -- See Note [Literals]
        -- unpackCString# is just a wrapper around a literal
        GHC.Var n `GHC.App` arg | GHC.getName n == GHC.unpackCStringName -> compileExpr arg
        -- See Note [unpackFoldrCString#]
        GHC.Var build `GHC.App` _ `GHC.App` GHC.Lam _ (GHC.Var unpack `GHC.App` _ `GHC.App` str)
            | GHC.getName build == GHC.buildName && GHC.getName unpack == GHC.unpackCStringFoldrName -> compileExpr str
        -- C# is just a wrapper around a literal
        GHC.Var (GHC.idDetails -> GHC.DataConWorkId dc) `GHC.App` arg | dc == GHC.charDataCon -> compileExpr arg
        -- void# - values of type void get represented as error, since they should be unreachable
        GHC.Var n | n == GHC.voidPrimId || n == GHC.voidArgId -> errorFunc
        -- See note [GHC runtime errors]
        -- <error func> <runtime rep> <overall type> <message>
        GHC.Var (isErrorId -> True) `GHC.App` _ `GHC.App` GHC.Type t `GHC.App` _ ->
            force =<< PIR.TyInst () <$> errorFunc <*> compileTypeNorm t
        -- <error func> <overall type> <message>
        GHC.Var (isErrorId -> True) `GHC.App` GHC.Type t `GHC.App` _ ->
            force =<< PIR.TyInst () <$> errorFunc <*> compileTypeNorm t
        -- See Note [Uses of Eq]
        GHC.Var n | GHC.getName n == GHC.eqName -> throwPlain $ UnsupportedError "Use of == from the Haskell Eq typeclass"
        GHC.Var n | GHC.getName n == GHC.eqIntegerPrimName -> throwPlain $ UnsupportedError "Use of Haskell Integer equality, possibly via the Haskell Eq typeclass"
        GHC.Var n | isProbablyBytestringEq n -> throwPlain $ UnsupportedError "Use of Haskell ByteString equality, possibly via the Haskell Eq typeclass"
        -- locally bound vars
        GHC.Var (lookupName top . GHC.getName -> Just var) -> pure $ PIR.mkVar () var
        -- Special kinds of id
        GHC.Var (GHC.idDetails -> GHC.PrimOpId po) -> compilePrimitiveOp po
        GHC.Var (GHC.idDetails -> GHC.DataConWorkId dc) -> compileDataConRef dc
        -- See Note [Unfoldings]
        -- The "unfolding template" includes things with normal unfoldings and also dictionary functions
        GHC.Var n@(GHC.maybeUnfoldingTemplate . GHC.realIdUnfolding -> Just unfolding) -> hoistExpr n unfolding
        -- Class ops don't have unfoldings in general (although they do if they're for one-method classes, so we
        -- want to check the unfoldings case first), see the GHC Note [ClassOp/DFun selection] for why. That
        -- means we have to reconstruct the RHS ourselves, though, which is a pain.
        GHC.Var n@(GHC.idDetails -> GHC.ClassOpId cls) -> do
            -- This code (mostly) lifted from MkId.mkDictSelId, which makes unfoldings for those dictionary
            -- selectors that do have them
            let sel_names = fmap GHC.getName (GHC.classAllSelIds cls)
            val_index <- case elemIndex (GHC.getName n) sel_names of
                Just i  -> pure i
                Nothing -> throwSd CompilationError $ "Id not in class method list:" GHC.<+> GHC.ppr n
            let rhs = GHC.mkDictSelRhs cls val_index

            hoistExpr n rhs
        GHC.Var n -> do
            -- Defined names, including builtin names
            maybeDef <- PIR.lookupTerm () (LexName $ GHC.getName n)
            case maybeDef of
                Just term -> pure term
                Nothing -> throwSd FreeVariableError $
                    "Variable" GHC.<+> GHC.ppr n
                    GHC.$+$ (GHC.ppr $ GHC.idDetails n)
                    GHC.$+$ (GHC.ppr $ GHC.realIdUnfolding n)
        GHC.Lit lit -> compileLiteral lit
        -- arg can be a type here, in which case it's a type instantiation
        l `GHC.App` GHC.Type t -> PIR.TyInst () <$> compileExpr l <*> compileTypeNorm t
        -- otherwise it's a normal application
        l `GHC.App` arg -> PIR.Apply () <$> compileExpr l <*> compileExpr arg
        -- if we're biding a type variable it's a type abstraction
        GHC.Lam b@(GHC.isTyVar -> True) body -> mkTyAbsScoped b $ compileExpr body
        -- othewise it's a normal lambda
        GHC.Lam b body -> mkLamAbsScoped b $ compileExpr body
        GHC.Let (GHC.NonRec b arg) body -> do
            -- the binding is in scope for the body, but not for the arg
            arg' <- compileExpr arg
            -- See Note [Non-strict let-bindings]
            let nonStrict = not $ PIR.isTermValue arg'
            withVarScoped b $ \v -> do
                let binds = [ PIR.TermBind () (if nonStrict then PIR.NonStrict else PIR.Strict) v arg' ]
                body' <- compileExpr body
                pure $ PIR.Let () PIR.NonRec binds body'
        GHC.Let (GHC.Rec bs) body ->
            withVarsScoped (fmap fst bs) $ \vars -> do
                -- the bindings are scope in both the body and the args
                -- TODO: this is a bit inelegant matching the vars back up
                binds <- for (zip vars bs) $ \(v, (_, arg)) -> do
                    arg' <- compileExpr arg
                    -- See Note [Non-strict let-bindings]
                    let nonStrict = not $ PIR.isTermValue arg'
                    pure $ PIR.TermBind () (if nonStrict then PIR.NonStrict else PIR.Strict) v arg'
                body' <- compileExpr body
                pure $ PIR.Let () PIR.Rec binds body'
        -- See Note [Default-only cases]
        GHC.Case scrutinee b _ [a@(_, _, body)] | GHC.isDefaultAlt a -> do
            -- See Note [At patterns]
            scrutinee' <- compileExpr scrutinee
            withVarScoped b $ \v -> do
                body' <- compileExpr body
                -- See Note [At patterns]
                let binds = [ PIR.TermBind () PIR.Strict v scrutinee' ]
                pure $ PIR.Let () PIR.NonRec binds body'
        GHC.Case scrutinee b t alts -> do
            -- See Note [At patterns]
            scrutinee' <- compileExpr scrutinee
            let scrutineeType = GHC.varType b

            -- the variable for the scrutinee is bound inside the cases, but not in the scrutinee expression itself
            withVarScoped b $ \v -> do
                (tc, argTys) <- case GHC.splitTyConApp_maybe scrutineeType of
                    Just (tc, argTys) -> pure (tc, argTys)
                    Nothing      -> throwSd UnsupportedError $ "Cannot case on a value of type:" GHC.<+> GHC.ppr scrutineeType
                dcs <- getDataCons tc

                -- See Note [Case expressions and laziness]
                isValueAlt <- forM dcs $ \dc ->
                    let (_, vars, body) = findAlt dc alts t
                    in if null vars then PIR.isTermValue <$> compileExpr body else pure True
                let lazyCase = not $ and isValueAlt

                match <- getMatchInstantiated scrutineeType
                let matched = PIR.Apply () match scrutinee'

                -- See Note [Scott encoding of datatypes]
                -- we're going to delay the body, so the scrutinee needs to be instantiated the delayed type
                resultType <- compileTypeNorm t >>= maybeDelayType lazyCase
                let instantiated = PIR.TyInst () matched resultType

                branches <- forM dcs $ \dc ->
                    let alt = findAlt dc alts t
                        -- these are the instantiated type arguments, e.g. for the data constructor Just when
                        -- matching on Maybe Int it is [Int] (crucially, not [a])
                        instArgTys = GHC.dataConInstOrigArgTys dc argTys
                    in compileAlt lazyCase instArgTys alt

                let applied = PIR.mkIterApp () instantiated branches
                -- See Note [Case expressions and laziness]
                mainCase <- maybeForce lazyCase applied

                -- See Note [At patterns]
                let binds = [ PIR.TermBind () PIR.Strict v scrutinee' ]
                pure $ PIR.Let () PIR.NonRec binds mainCase
        -- we can use source notes to get a better context for the inner expression
        -- these are put in when you compile with -g
        GHC.Tick GHC.SourceNote{GHC.sourceSpan=src} body ->
            withContextM 1 (sdToTxt $ "Compiling expr at:" GHC.<+> GHC.ppr src) $ compileExpr body
        -- ignore other annotations
        GHC.Tick _ body -> compileExpr body
        -- See Note [Coercions and newtypes]
        GHC.Cast body _ -> compileExpr body
        GHC.Type _ -> throwPlain $ UnsupportedError "Types as standalone expressions"
        GHC.Coercion _ -> throwPlain $ UnsupportedError "Coercions as expressions"

compileExprWithDefs :: Compiling m => GHC.CoreExpr -> m PIRTerm
compileExprWithDefs e = do
    defineBuiltinTypes
    defineBuiltinTerms
    compileExpr e
