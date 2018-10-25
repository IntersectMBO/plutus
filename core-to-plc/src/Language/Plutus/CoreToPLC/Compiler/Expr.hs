{-# LANGUAGE ConstraintKinds   #-}
{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ViewPatterns      #-}

-- | Functions for compiling GHC Core expressions into Plutus Core terms.
module Language.Plutus.CoreToPLC.Compiler.Expr (convExpr, convExprWithDefs) where

import           Language.Plutus.CoreToPLC.Compiler.Binders
import           Language.Plutus.CoreToPLC.Compiler.Builtins
import           Language.Plutus.CoreToPLC.Compiler.Definitions
import           Language.Plutus.CoreToPLC.Compiler.Names
import           Language.Plutus.CoreToPLC.Compiler.Primitives
import           Language.Plutus.CoreToPLC.Compiler.Type
import           Language.Plutus.CoreToPLC.Compiler.Types
import           Language.Plutus.CoreToPLC.Compiler.Utils
import           Language.Plutus.CoreToPLC.Error
import           Language.Plutus.CoreToPLC.Laziness
import           Language.Plutus.CoreToPLC.PLCTypes
import           Language.Plutus.CoreToPLC.Utils

import qualified CoreUtils                                      as GHC
import qualified GhcPlugins                                     as GHC
import qualified MkId                                           as GHC
import qualified PrelNames                                      as GHC

import qualified Language.PlutusCore                            as PLC
import           Language.PlutusCore.MkPlc
import           Language.PlutusCore.Quote
import qualified Language.PlutusCore.StdLib.Data.Function       as Function

import           Control.Monad.Reader
import           Control.Monad.State

import qualified Data.ByteString.Lazy                           as BSL
import qualified Data.List.NonEmpty                             as NE
import qualified Data.Map                                       as Map

import           Data.List                                      (elemIndex)

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


{- Note [Recursive lets]
We need to define these with a fixpoint. We can derive a fixpoint operator for values
already.

However, we also need to work out how to encode recursion over multiple values simultaneously.
The answer is simple - we pass them through as a tuple.

Overall, the translation looks like this. We convert this:

let rec
  f_1 = b_1
  ...
  f_i = b_i
in
  result

into this:

($fixN i$ (\choose f1 ... fi . choose b_1 ... b_i))
(\f1 ... fi . result)
-}

-- Expressions

convExpr :: Converting m => GHC.CoreExpr -> m PLCTerm
convExpr e = withContextM (sdToTxt $ "Converting expr:" GHC.<+> GHC.ppr e) $ do
    -- See Note [Scopes]
    ConvertingContext {ccPrimTerms=prims, ccScopes=stack} <- ask
    let top = NE.head stack
    case e of
        -- See Note [Literals]
        GHC.App (GHC.Var (isPrimitiveWrapper -> True)) arg -> convExpr arg
        -- special typeclass method calls
        GHC.App (GHC.App
                -- eq class method
                (GHC.Var n@(GHC.idDetails -> GHC.ClassOpId ((==) GHC.eqClassName . GHC.getName -> True)))
                -- we only support applying to int
                (GHC.Type (GHC.eqType GHC.intTy -> True)))
            -- last arg is typeclass dictionary
            _ -> convEqMethod (GHC.getName n)
        GHC.App (GHC.App
                -- ord class method
                (GHC.Var n@(GHC.idDetails -> GHC.ClassOpId ((==) GHC.ordClassName . GHC.getName -> True)))
                -- we only support applying to int
                (GHC.Type (GHC.eqType GHC.intTy -> True)))
            -- last arg is typeclass dictionary
            _ -> convOrdMethod (GHC.getName n)
        GHC.App (GHC.App
                -- num class method
                (GHC.Var n@(GHC.idDetails -> GHC.ClassOpId ((==) GHC.numClassName . GHC.getName -> True)))
                -- we only support applying to int
                (GHC.Type (GHC.eqType GHC.intTy -> True)))
            -- last arg is typeclass dictionary
            _ -> convNumMethod (GHC.getName n)
        -- void# - values of type void get represented as error, since they should be unreachable
        GHC.Var n | n == GHC.voidPrimId || n == GHC.voidArgId -> liftQuote errorFunc
        -- locally bound vars
        GHC.Var (lookupName top . GHC.getName -> Just (PLCVar name _)) -> pure $ PLC.Var () name
        -- Special kinds of id
        GHC.Var (GHC.idDetails -> GHC.PrimOpId po) -> convPrimitiveOp po
        GHC.Var (GHC.idDetails -> GHC.DataConWorkId dc) ->
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
        GHC.Var (flip Map.lookup prims . GHC.getName -> Just term) -> liftQuote term
        -- the term we get must be closed - we don't resolve most references
        -- TODO: possibly relax this?
        GHC.Var n@(GHC.idDetails -> GHC.VanillaId) -> throwSd FreeVariableError $ "Variable:" GHC.<+> GHC.ppr n GHC.$+$ (GHC.ppr $ GHC.idDetails n)
        GHC.Var n -> throwSd UnsupportedError $ "Variable" GHC.<+> GHC.ppr n GHC.$+$ (GHC.ppr $ GHC.idDetails n)
        GHC.Lit lit -> PLC.Constant () <$> convLiteral lit
        -- arg can be a type here, in which case it's a type instantiation
        GHC.App l (GHC.Type t) -> PLC.TyInst () <$> convExpr l <*> convType t
        -- otherwise it's a normal application
        GHC.App l arg -> PLC.Apply () <$> convExpr l <*> convExpr arg
        -- if we're biding a type variable it's a type abstraction
        GHC.Lam b@(GHC.isTyVar -> True) body -> mkTyAbsScoped b $ convExpr body
        -- othewise it's a normal lambda
        GHC.Lam b body -> mkLamAbsScoped b $ convExpr body
        GHC.Let (GHC.NonRec b arg) body -> do
            -- convert it as a lambda
            a' <- convExpr arg
            l' <- mkLamAbsScoped b $ convExpr body
            pure $ PLC.Apply () l' a'
        GHC.Let (GHC.Rec bs) body -> do
            -- See note [Recursive lets]
            -- TODO: we're technically using these twice, which is bad and maybe we need to duplicate
            tys <- mapM convType (fmap (GHC.varType . fst) bs)
            -- The pairs of types we'll need for fixN
            asbs <- forM tys $ \case
                PLC.TyFun () i o -> pure (i, o)
                _ -> throwPlain $ ConversionError "Recursive values must be of function type. You may need to manually add unit arguments."

            -- We need this so we can use the tuple of recursive functions in the end - it
            -- expects an output type.
            outTy <- convType (GHC.exprType body)

            q <- safeFreshTyName "Q"
            choose <- safeFreshName "choose"
            let chooseTy = mkIterTyFun tys (PLC.TyVar () q)

            -- \f1 ... fn -> choose b1 ... bn
            bsLam <- mkIterLamAbsScoped (fmap fst bs) $ do
                rhss <- mapM convExpr (fmap snd bs)
                pure $ mkIterApp (PLC.Var() choose) rhss

            -- abstract out Q and choose
            let cLam = PLC.TyAbs () q (PLC.Type ()) $ PLC.LamAbs () choose chooseTy bsLam

            -- fixN {A1 B1 ... An Bn}
            instantiatedFix <- do
                fixN <- liftQuote $ Function.getBuiltinFixN (length bs)
                pure $ mkIterInst fixN $ foldMap (\(a, b) -> [a, b]) asbs

            let fixed = PLC.Apply () instantiatedFix cLam

            -- the consumer of the recursive functions
            bodyLam <- mkIterLamAbsScoped (fmap fst bs) (convExpr body)
            pure $ PLC.Apply () (PLC.TyInst () fixed outTy) bodyLam
        GHC.Case scrutinee b t alts -> do
            let scrutineeType = GHC.varType b

            -- See Note [Case expressions and laziness]
            isValueAlt <- mapM (\(_, vars, body) -> if null vars then PLC.isTermValue <$> convExpr body else pure True) alts
            let lazyCase = not $ and isValueAlt

            scrutinee' <- convExpr scrutinee

            match <- getMatchInstantiated scrutineeType
            let matched = PLC.Apply () match scrutinee'

            -- See Note [Scott encoding of datatypes]
            -- we're going to delay the body, so the scrutinee needs to be instantiated the delayed type
            instantiated <- PLC.TyInst () matched <$> (convType t >>= maybeDelayType lazyCase)

            tc <- case GHC.splitTyConApp_maybe scrutineeType of
                Just (tc, _) -> pure tc
                Nothing      -> throwPlain $ ConversionError "Scrutinee's type was not a type constructor application"
            dcs <- getDataCons tc

            branches <- forM dcs $ \dc -> case GHC.findAlt (GHC.DataAlt dc) alts of
                Just alt -> convAlt lazyCase dc alt
                Nothing  -> throwPlain $ ConversionError "No case matched and no default case"

            let applied = mkIterApp instantiated branches
            -- See Note [Case expressions and laziness]
            maybeForce lazyCase applied
        -- ignore annotation
        GHC.Tick _ body -> convExpr body
        GHC.Cast body coerce -> do
            body' <- convExpr body
            case splitNewtypeCoercion coerce of
                Just (Unwrap outer inner) -> do
                    match <- getMatchInstantiated outer
                    -- unwrap by doing a "trivial match" - instantiate to the inner type and apply the identity
                    inner' <- convType inner
                    let instantiated = PLC.TyInst () (PLC.Apply () match body') inner'
                    name <- safeFreshName "inner"
                    let identity = PLC.LamAbs () name inner' (PLC.Var () name)
                    pure $ PLC.Apply () instantiated identity
                Just (Wrap _ outer) -> do
                    constr <- head <$> getConstructorsInstantiated outer
                    pure $ PLC.Apply () constr body'
                _ -> throwSd UnsupportedError $ "Coercion" GHC.$+$ GHC.ppr coerce
        GHC.Type _ -> throwPlain $ ConversionError "Cannot convert types directly, only as arguments to applications"
        GHC.Coercion _ -> throwPlain $ ConversionError "Coercions should not be converted"

convExprWithDefs :: Converting m => GHC.CoreExpr -> m PLCTerm
convExprWithDefs e = do
    converted <- convExpr e
    ConvertingState{csTypeDefs=typeDs, csTermDefs=termDs} <- get
    wrapWithDefs typeDs termDs converted
