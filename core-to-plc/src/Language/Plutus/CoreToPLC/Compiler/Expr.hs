{-# LANGUAGE ConstraintKinds   #-}
{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ViewPatterns      #-}

-- | Functions for compiling GHC Core expressions into Plutus Core terms.
module Language.Plutus.CoreToPLC.Compiler.Expr (convExpr, convExprWithDefs, convDataConRef) where

import           Language.Plutus.CoreToPLC.Compiler.Binders
import           Language.Plutus.CoreToPLC.Compiler.Builtins
import           Language.Plutus.CoreToPLC.Compiler.Definitions
import           Language.Plutus.CoreToPLC.Compiler.Error
import           Language.Plutus.CoreToPLC.Compiler.Laziness
import           Language.Plutus.CoreToPLC.Compiler.Names
import           Language.Plutus.CoreToPLC.Compiler.Primitives
import           Language.Plutus.CoreToPLC.Compiler.Type
import           Language.Plutus.CoreToPLC.Compiler.Types
import           Language.Plutus.CoreToPLC.Compiler.Utils
import           Language.Plutus.CoreToPLC.PIRTypes
import           Language.Plutus.CoreToPLC.Utils

import qualified CoreUtils                                      as GHC
import qualified GhcPlugins                                     as GHC
import qualified MkId                                           as GHC
import qualified PrelNames                                      as GHC

import qualified Language.PlutusIR                              as PIR
import qualified Language.PlutusIR.MkPir                        as PIR
import qualified Language.PlutusIR.Value                        as PIR

import qualified Language.PlutusCore                            as PLC

import           Control.Monad.Reader
import           Control.Monad.State

import qualified Data.ByteString.Lazy                           as BSL
import           Data.List                                      (elem, elemIndex)
import qualified Data.List.NonEmpty                             as NE
import           Data.Traversable

{- Note [System FC and System FW]
Haskell uses system FC, which includes type equalities and coercions.

PLC does *not* have coercions in particular. However, PLC also does not have a nominal
type system - everything is constructed via operators on base types, so we have no
need for coercions to convert between newtypes and datatypes.

So we mostly ignore coercions. The one place that I know of where the mismatch hurts
us is that GHC uses the `Any` type (coercible to and from anything) for unconstrained
function variables, e.g. in polymorphic lambdas. This is annoying for us, since we
really want the version with explicit type abstraction. I don't currently have a fix
for this.
-}


-- Literals and primitives

{- Note [Literals]
GHC's literals and primitives are a bit of a pain, since they not only have a Literal
containing the actual data, but are wrapped in special functions (often ending in the magic #).

This is a pain to recognize.
-}

convLiteral :: Converting m => GHC.Literal -> m (PLC.Constant ())
convLiteral l = case l of
    -- TODO: better sizes
    GHC.MachInt64 i    -> pure $ PLC.BuiltinInt () haskellIntSize i
    GHC.MachInt i      -> pure $ PLC.BuiltinInt () haskellIntSize i
    GHC.MachStr bs     -> pure $ PLC.BuiltinBS () haskellBSSize (BSL.fromStrict bs)
    GHC.LitInteger _ _ -> throwPlain $ UnsupportedError "Literal (unbounded) integer"
    GHC.MachWord _     -> throwPlain $ UnsupportedError "Literal word"
    GHC.MachWord64 _   -> throwPlain $ UnsupportedError "Literal word64"
    GHC.MachChar _     -> throwPlain $ UnsupportedError "Literal char"
    GHC.MachFloat _    -> throwPlain $ UnsupportedError "Literal float"
    GHC.MachDouble _   -> throwPlain $ UnsupportedError "Literal double"
    GHC.MachLabel {}   -> throwPlain $ UnsupportedError "Literal label"
    GHC.MachNullAddr   -> throwPlain $ UnsupportedError "Literal null"

isPrimitiveWrapper :: GHC.Id -> Bool
isPrimitiveWrapper i = case GHC.idDetails i of
    GHC.DataConWorkId dc -> isPrimitiveDataCon dc
    GHC.VanillaId        -> GHC.getName i == GHC.unpackCStringName
    _                    -> False

isPrimitiveDataCon :: GHC.DataCon -> Bool
isPrimitiveDataCon dc = dc == GHC.intDataCon

-- | Convert a reference to a data constructor, i.e. a call to it.
convDataConRef :: Converting m => GHC.DataCon -> m PIRTerm
convDataConRef dc =
    let
        tc = GHC.dataConTyCon dc
    in do
        dcs <- getDataCons tc
        constrs <- getConstructors tc

        -- TODO: this is inelegant
        index <- case elemIndex dc dcs of
            Just i  -> pure i
            Nothing -> throwPlain $ ConversionError "Data constructor not in the type constructor's list of constructors!"

        pure $ constrs !! index

isErrorId :: GHC.Id -> Bool
isErrorId ghcId = ghcId `elem` GHC.errorIds

{- Note [GHC runtime errors]
GHC has a number of runtime errors for things like pattern matching failures and so on.

We just translate these directly into calls to error, throwing away any other information.

Annoyingly, unlike void, we can't mangle the type uniformly to make sure we are safe
with respect to the value restriction (see note [Value restriction]), so we just have to force
our error call and hope that it doesn't end up somewhere it shouldn't.
-}

{- Note [At patterns]
GHC handles @-patterns by adding a variable to each case expression representing the scrutinee
of the expression.

We handle this by simply let-binding that variable outside our generated case. In the instances
where it's not used, the PIR dead-binding pass will remove it.
-}

-- Expressions

convExpr :: Converting m => GHC.CoreExpr -> m PIRTerm
convExpr e = withContextM (sdToTxt $ "Converting expr:" GHC.<+> GHC.ppr e) $ do
    -- See Note [Scopes]
    ConvertingContext {ccScopes=stack} <- ask
    let top = NE.head stack
    case e of
        -- See Note [Literals]
        GHC.App (GHC.Var (isPrimitiveWrapper -> True)) arg -> convExpr arg
        -- special typeclass method calls
        GHC.App (GHC.App
                (GHC.Var n@(GHC.idDetails -> GHC.ClassOpId (GHC.getName -> className)))
                -- we only support applying to int
                (GHC.Type (GHC.eqType GHC.intTy -> True)))
            -- last arg is typeclass dictionary
            _ -> case className of
                     ((==) GHC.eqClassName -> True) -> convEqMethod (GHC.getName n)
                     ((==) GHC.ordClassName -> True) -> convOrdMethod (GHC.getName n)
                     ((==) GHC.numClassName -> True) -> convNumMethod (GHC.getName n)
                     ((==) GHC.integralClassName -> True) -> convIntegralMethod (GHC.getName n)
                     _ -> throwSd UnsupportedError $ "Typeclass method:" GHC.<+> GHC.ppr n
        -- void# - values of type void get represented as error, since they should be unreachable
        GHC.Var n | n == GHC.voidPrimId || n == GHC.voidArgId -> errorFunc
        -- See note [GHC runtime errors]
        GHC.App (GHC.App (GHC.App
                -- error function
                (GHC.Var (isErrorId -> True))
                -- runtime rep
                _)
                -- type of overall expression
                (GHC.Type t))
            _ -> force =<< PIR.TyInst () <$> errorFunc <*> convType t
        -- locally bound vars
        GHC.Var (lookupName top . GHC.getName -> Just (PIR.VarDecl _ name _)) -> pure $ PIR.Var () name
        -- Special kinds of id
        GHC.Var (GHC.idDetails -> GHC.PrimOpId po) -> convPrimitiveOp po
        GHC.Var (GHC.idDetails -> GHC.DataConWorkId dc) -> convDataConRef dc
        -- TODO: support record selectors. AFAICT GHC doesn't make a pattern-matching function that we can call, so we'd
        -- have to make the pattern match ourselves
        GHC.Var (GHC.idDetails -> GHC.RecSelId{}) -> throwPlain $ UnsupportedError "Record selectors, use pattern matching"
        GHC.Var n -> do
            -- Defined names, including builtin names
            maybeDef <- lookupTermDef (GHC.getName n)
            case maybeDef of
                Just term -> pure term
                -- the term we get must be closed - we don't resolve most references
                -- TODO: possibly relax this?
                Nothing -> throwSd FreeVariableError $ "Variable" GHC.<+> GHC.ppr n GHC.$+$ (GHC.ppr $ GHC.idDetails n)
        GHC.Lit lit -> PIR.Constant () <$> convLiteral lit
        -- arg can be a type here, in which case it's a type instantiation
        GHC.App l (GHC.Type t) -> PIR.TyInst () <$> convExpr l <*> convType t
        -- otherwise it's a normal application
        GHC.App l arg -> PIR.Apply () <$> convExpr l <*> convExpr arg
        -- if we're biding a type variable it's a type abstraction
        GHC.Lam b@(GHC.isTyVar -> True) body -> mkTyAbsScoped b $ convExpr body
        -- othewise it's a normal lambda
        GHC.Lam b body -> mkLamAbsScoped b $ convExpr body
        GHC.Let (GHC.NonRec b arg) body -> do
            -- the binding is in scope for the body, but not for the arg
            arg' <- convExpr arg
            withVarScoped b $ \v -> do
                let binds = [ PIR.TermBind () v arg' ]
                body' <- convExpr body
                pure $ PIR.Let () PIR.NonRec binds body'
        GHC.Let (GHC.Rec bs) body ->
            withVarsScoped (fmap fst bs) $ \vars -> do
                -- the bindings are scope in both the body and the args
                -- TODO: this is a bit inelegant matching the vars back up
                binds <- for (zip vars bs) $ \(v, (_, arg)) -> do
                    arg' <- convExpr arg
                    pure $ PIR.TermBind () v arg'
                body' <- convExpr body
                pure $ PIR.Let () PIR.Rec binds body'
        GHC.Case scrutinee b t alts -> do
            -- See Note [At patterns]
            scrutinee' <- convExpr scrutinee
            let scrutineeType = GHC.varType b

            -- the variable for the scrutinee is bound inside the cases, but not in the scrutinee expression itself
            withVarScoped b $ \v -> do
                -- See Note [Case expressions and laziness]
                isValueAlt <- forM alts (\(_, vars, body) -> if null vars then PIR.isTermValue <$> convExpr body else pure True)
                let lazyCase = not $ and isValueAlt

                match <- getMatchInstantiated scrutineeType
                let matched = PIR.Apply () match scrutinee'

                -- See Note [Scott encoding of datatypes]
                -- we're going to delay the body, so the scrutinee needs to be instantiated the delayed type
                instantiated <- PIR.TyInst () matched <$> (convType t >>= maybeDelayType lazyCase)

                (tc, argTys) <- case GHC.splitTyConApp_maybe scrutineeType of
                    Just (tc, argTys) -> pure (tc, argTys)
                    Nothing      -> throwPlain $ ConversionError "Scrutinee's type was not a type constructor application"
                dcs <- getDataCons tc

                branches <- forM dcs $ \dc -> case GHC.findAlt (GHC.DataAlt dc) alts of
                    Just alt ->
                        let
                            -- these are the instantiated type arguments, e.g. for the data constructor Just when
                            -- matching on Maybe Int it is [Int] (crucially, not [a])
                            instArgTys = GHC.dataConInstOrigArgTys dc argTys
                        in convAlt lazyCase instArgTys alt
                    Nothing  -> throwPlain $ ConversionError "No case matched and no default case"

                let applied = PIR.mkIterApp () instantiated branches
                -- See Note [Case expressions and laziness]
                mainCase <- maybeForce lazyCase applied

                -- See Note [At patterns]
                let binds = [ PIR.TermBind () v scrutinee' ]
                pure $ PIR.Let () PIR.NonRec binds mainCase
        -- ignore annotation
        GHC.Tick _ body -> convExpr body
        GHC.Cast body coerce -> do
            body' <- convExpr body
            case splitNewtypeCoercion coerce of
                Just (Unwrap outer inner) -> do
                    match <- getMatchInstantiated outer
                    -- unwrap by doing a "trivial match" - instantiate to the inner type and apply the identity
                    inner' <- convType inner
                    let instantiated = PIR.TyInst () (PIR.Apply () match body') inner'
                    name <- safeFreshName "inner"
                    let identity = PIR.LamAbs () name inner' (PIR.Var () name)
                    pure $ PIR.Apply () instantiated identity
                Just (Wrap _ outer) -> do
                    constr <- head <$> getConstructorsInstantiated outer
                    pure $ PIR.Apply () constr body'
                _ -> throwSd UnsupportedError $ "Coercion" GHC.$+$ GHC.ppr coerce
        GHC.Type _ -> throwPlain $ ConversionError "Cannot convert types directly, only as arguments to applications"
        GHC.Coercion _ -> throwPlain $ ConversionError "Coercions should not be converted"

convExprWithDefs :: Converting m => GHC.CoreExpr -> m PIRTerm
convExprWithDefs e = do
    defineBuiltinTypes
    defineBuiltinTerms
    converted <- convExpr e
    ds <- gets csDefs
    wrapWithDefs ds converted
