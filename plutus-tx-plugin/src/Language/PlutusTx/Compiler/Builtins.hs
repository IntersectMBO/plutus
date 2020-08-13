{-# LANGUAGE ConstraintKinds   #-}
{-# LANGUAGE DataKinds         #-}
{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell   #-}
{-# LANGUAGE TypeApplications  #-}
{-# LANGUAGE TypeOperators     #-}
{-# LANGUAGE ViewPatterns      #-}

-- | Functions for compiling Plutus Core builtins.
module Language.PlutusTx.Compiler.Builtins (
    builtinNames
    , defineBuiltinTypes
    , defineBuiltinTerms
    , lookupBuiltinTerm
    , lookupBuiltinType
    , errorTy
    , errorFunc) where

import qualified Language.PlutusTx.Builtins             as Builtins
import qualified Language.PlutusTx.String               as String

import           Language.PlutusTx.Compiler.Error
import {-# SOURCE #-} Language.PlutusTx.Compiler.Expr
import           Language.PlutusTx.Compiler.Laziness
import           Language.PlutusTx.Compiler.Names
import {-# SOURCE #-} Language.PlutusTx.Compiler.Type
import           Language.PlutusTx.Compiler.Types
import           Language.PlutusTx.Compiler.Utils
import           Language.PlutusTx.PIRTypes

import qualified Language.PlutusIR                      as PIR
import qualified Language.PlutusIR.Compiler.Definitions as PIR
import           Language.PlutusIR.Compiler.Names
import qualified Language.PlutusIR.MkPir                as PIR
import qualified Language.PlutusIR.Purity               as PIR

import qualified Language.PlutusCore                    as PLC
import qualified Language.PlutusCore.Constant           as PLC
import qualified Language.PlutusCore.Constant.Dynamic   as PLC
import           Language.PlutusCore.Quote
import qualified Language.PlutusCore.StdLib.Data.Bool   as Bool
import qualified Language.PlutusCore.StdLib.Data.Unit   as Unit

import qualified GhcPlugins                             as GHC

import qualified Language.Haskell.TH.Syntax             as TH

import           Control.Monad
import           Control.Monad.Reader

import qualified Data.ByteString.Lazy                   as BSL
import qualified Data.Map                               as Map
import           Data.Proxy
import qualified Data.Set                               as Set

{- Note [Mapping builtins]
We want the user to be able to call the Plutus builtins as normal Haskell functions.

To do this, we provide a library of such functions in Haskell, and we define corresponding
functions and types in PIR so that we can translate references to the Haskell functions and
types into references to the PIR ones.

We can then do whatever we need to inside the definitions to line things up with the real builtins.
(See Note [Builtin types and Haskell types])

To do this, we first need a map from the Haskell TH names to the corresponding GHC names
(in fact the TyThings, so we have the types too). Annoyingly, this has to be done in the
GHC Core monad and then passed to us.

This map lets us write code that defines all the builtins (by their TH names), and also to look
up things by their TH names in the few other cases where we need to (mostly where we use specific
known builtins to implement primitives).

This is a bit fragile, since we rely on having all the names that we need, and having them
mapped to the right things (GHC will panic on us if we e.g. get the wrong kind of TyThing for
a name). We should probably revisit this later.
-}

{- Note [Builtin types and Haskell types]
Several of the PLC builtins use types that should (morally) line up with types that we compile from
Haskell (see also Note [Which types map to builtin types?]).
But there is a problem: they use either primitive or Scott-encoded versions of these types,
whereas when we compile them from Haskell they will end up as abstract types, and so the types
won't line up at the call site.

That is, we generate something like this:
(/\ (Integer :: *) .
  (\ addInteger : Integer -> Integer -> Integer .
      <use addInteger>
  )
  (\ x,y : Integer . <builtin addInteger> x y) -- Uh oh, type error, can't show that Integer = <builtin int>!
)
{<builtin int>}

We handle this in two different ways:
- For the types like Bool and Unit which are really algebraic types, and which have constructors etc.
that we care about elsewhere, we insert adaptor code into the definition of the builtin (see note [Mapping builtins]).
- For types like Integer and Bytestring which don't have visible constructors, we can treat them as completely opaque,
and we use a transparent type alias. (Actually we fake the alias by actually just substituting the definition in
everywhere until we have aliases in PIR. Bear this in mind for the examples below.)

Here's how that looks for a primitive that takes Ints and returns a Boolean, assuming we have bound Integer and Bool
already as an alias and an abstract type respectively:
(\ equalsInteger : Integer -> Integer -> Bool .
  <use equalsInteger>
)
(\ x, y : Integer . -- No need to do anything to the arguments, since we're using a transparent alias for Int
  (<builtin equalsInteger> x y) {Bool} True False -- Immediately match the builtin bool into an abstract Bool
)

We *could* do something like the interleaved definitions that we do for datatypes in PIR. Morally this is perhaps the
right thing to do: we should think of Integer and its builtins as a "module" that goes together and where all the definitions
have access to the internals of the other definitions. A datatype definition is then a special case of a module definition.
However, for the moment this would be quite a bit more design work and so we leave it for future work.

For an example of how the "abstract module" approach would look:
(/\ (Integer :: *) .
  (\ addInteger : Integer -> Integer -> Integer . -- Type signature is fine inside the abstraction
      <use addInteger>
  )
)
{<builtin int>}
(\ x,y : <builtin int> . <builtin addInteger> x y) -- No type error any more, abstraction is gone
-}

{- Note [Which types map to builtin types?]
We have (will have) Bool in the default builtin universe. Why do we not map the Haskell Bool type to the
builtin Bool, but rather compile it as a normal ADT?

The advantage of mapping a type to a builtin type is mainly performance:
- We can directly use (potentially optimized) implementations of operations on that type.
- We do not need adaptors to interoperate with builtin functions that use the builtin version of the type.

On the other hand, the advantages of *not* doing this are:
- User-written code that operates on the type as normal (e.g. pattern matching) will work.
    - We could make this work by compiling pattern matching specially for the builtin type, but this means
      more special cases in the compiler (boo). Maybe we can do this generically in future.
- Code that uses these types will also be compilable/runnable if those builtins are not present.

Overall, this means that we only map performance-critical types like Integer and ByteString directly to
builtin types, and the others we compile normally.
-}

{- Note [Builtin terms and values]
When generating let-bindings, we would like to generate strict bindings only for things that are obviously
pure, and non-strict bindings otherwise. This ensures that we won't evaluate the RHS of the binding prematurely,
which matters if it could trigger an error, or some other effect.

Additionally, strict bindings are a bit more efficient than non-strict ones (non-strict ones get turned into
lambdas from unit and forcing in the body). So we would like to use strict bindings where possible.

Now, we generate bindings for all our builtin functions... but they are not *obviously* pure!
Fortunately, we have a more sophisticated purity check that also detects unsaturated builtin applications,
which handles these cases too.
-}

mkStaticBuiltin :: PLC.StaticBuiltinName -> PIR.Term tyname name uni ()
mkStaticBuiltin n = PIR.Builtin () $ PLC.StaticBuiltinName n

mkDynBuiltin :: PLC.DynamicBuiltinName -> PIR.Term tyname name uni ()
mkDynBuiltin n = PIR.Builtin () $ PLC.DynBuiltinName n

-- | The 'TH.Name's for which 'BuiltinNameInfo' needs to be provided.
builtinNames :: [TH.Name]
builtinNames = [
      ''Builtins.ByteString
    , ''Integer
    , ''Bool
    , ''()

    , 'Builtins.concatenate
    , 'Builtins.takeByteString
    , 'Builtins.dropByteString
    , 'Builtins.sha2_256
    , 'Builtins.sha3_256
    , 'Builtins.equalsByteString
    , 'Builtins.lessThanByteString
    , 'Builtins.greaterThanByteString
    , 'Builtins.emptyByteString

    , 'Builtins.verifySignature

    , 'Builtins.addInteger
    , 'Builtins.subtractInteger
    , 'Builtins.multiplyInteger
    , 'Builtins.divideInteger
    , 'Builtins.remainderInteger
    , 'Builtins.greaterThanInteger
    , 'Builtins.greaterThanEqInteger
    , 'Builtins.lessThanInteger
    , 'Builtins.lessThanEqInteger
    , 'Builtins.equalsInteger

    , 'Builtins.error

    , ''Builtins.String
    , ''Char
    , 'Builtins.appendString
    , 'Builtins.emptyString
    , 'Builtins.charToString
    , 'String.stringToBuiltinString

    , 'Builtins.trace
    ]

-- | Get the 'GHC.TyThing' for a given 'TH.Name' which was stored in the builtin name info,
-- failing if it is missing.
getThing :: Compiling uni m => TH.Name -> m GHC.TyThing
getThing name = do
    CompileContext{ccBuiltinNameInfo=names} <- ask
    case Map.lookup name names of
        Nothing    -> throwSd CompilationError $ "Missing builtin name:" GHC.<+> (GHC.text $ show name)
        Just thing -> pure thing

defineBuiltinTerm :: Compiling uni m => TH.Name -> PIRTerm uni -> [GHC.Name] -> m ()
defineBuiltinTerm name term deps = do
    ghcId <- GHC.tyThingId <$> getThing name
    var <- compileVarFresh ghcId
    CompileContext {ccBuiltinMeanings=means} <- ask
    -- See Note [Builtin terms and values]
    let strictness = if PIR.isPure means (const PIR.NonStrict) term then PIR.Strict else PIR.NonStrict
        def = PIR.Def var (term, strictness)
    PIR.defineTerm (LexName $ GHC.getName ghcId) def (Set.fromList $ LexName <$> deps)

-- | Add definitions for all the builtin types to the environment.
defineBuiltinType :: forall uni m. Compiling uni m => TH.Name -> PIRType uni -> [GHC.Name] -> m ()
defineBuiltinType name ty deps = do
    tc <- GHC.tyThingTyCon <$> getThing name
    var <- compileTcTyVarFresh tc
    PIR.defineType (LexName $ GHC.getName tc) (PIR.Def var ty) (Set.fromList $ LexName <$> deps)
    -- these are all aliases for now
    PIR.recordAlias @LexName @uni @() (LexName $ GHC.getName tc)

-- | Add definitions for all the builtin terms to the environment.
defineBuiltinTerms :: Compiling uni m => m ()
defineBuiltinTerms = do
    bs <- GHC.getName <$> getThing ''Builtins.ByteString
    int <- GHC.getName <$> getThing ''Integer
    bool <- GHC.getName <$> getThing ''Bool
    unit <- GHC.getName <$> getThing ''()
    str <- GHC.getName <$> getThing ''Builtins.String
    char <- GHC.getName <$> getThing ''Char

    intTy <- lookupBuiltinType ''Integer
    bsTy <- lookupBuiltinType ''Builtins.ByteString
    strTy <- lookupBuiltinType ''Builtins.String

    -- See Note [Builtin terms and values] for the eta expansion below

    -- Bytestring builtins
    do
        let term = mkStaticBuiltin PLC.Concatenate
        defineBuiltinTerm 'Builtins.concatenate term [bs]
    do
        let term = mkStaticBuiltin PLC.TakeByteString
        defineBuiltinTerm 'Builtins.takeByteString term [int, bs]
    do
        let term = mkStaticBuiltin PLC.DropByteString
        defineBuiltinTerm 'Builtins.dropByteString term [int, bs]
    do
        let term = mkStaticBuiltin PLC.SHA2
        defineBuiltinTerm 'Builtins.sha2_256 term [bs]
    do
        let term = mkStaticBuiltin PLC.SHA3
        defineBuiltinTerm 'Builtins.sha3_256 term [bs]
    do
        term <- wrapRel bsTy 2 $ mkStaticBuiltin PLC.EqByteString
        defineBuiltinTerm 'Builtins.equalsByteString term [bs, bool]
    do
        term <- wrapRel bsTy 2 $ mkStaticBuiltin PLC.LtByteString
        defineBuiltinTerm 'Builtins.lessThanByteString term [bs, bool]
    do
        term <- wrapRel bsTy 2 $ mkStaticBuiltin PLC.GtByteString
        defineBuiltinTerm 'Builtins.greaterThanByteString term [bs, bool]

    do
        let term = PIR.mkConstant () BSL.empty
        defineBuiltinTerm 'Builtins.emptyByteString term [bs]

    -- Integer builtins
    do
        let term = mkStaticBuiltin PLC.AddInteger
        defineBuiltinTerm 'Builtins.addInteger term [int]
    do
        let term = mkStaticBuiltin PLC.SubtractInteger
        defineBuiltinTerm 'Builtins.subtractInteger term [int]
    do
        let term = mkStaticBuiltin PLC.MultiplyInteger
        defineBuiltinTerm 'Builtins.multiplyInteger term [int]
    do
        let term = mkStaticBuiltin PLC.DivideInteger
        defineBuiltinTerm 'Builtins.divideInteger term [int]
    do
        let term = mkStaticBuiltin PLC.RemainderInteger
        defineBuiltinTerm 'Builtins.remainderInteger term [int]
    do
        term <- wrapRel intTy 2 $ mkStaticBuiltin PLC.GreaterThanInteger
        defineBuiltinTerm 'Builtins.greaterThanInteger term [int, bool]
    do
        term <- wrapRel intTy 2 $ mkStaticBuiltin PLC.GreaterThanEqInteger
        defineBuiltinTerm 'Builtins.greaterThanEqInteger term [int, bool]
    do
        term <- wrapRel intTy 2 $ mkStaticBuiltin PLC.LessThanInteger
        defineBuiltinTerm 'Builtins.lessThanInteger term [int, bool]
    do
        term <- wrapRel intTy 2 $ mkStaticBuiltin PLC.LessThanEqInteger
        defineBuiltinTerm 'Builtins.lessThanEqInteger term [int, bool]
    do
        term <- wrapRel intTy 2 $ mkStaticBuiltin PLC.EqInteger
        defineBuiltinTerm 'Builtins.equalsInteger term [int, bool]

    -- Blockchain builtins
    do
        term <- wrapRel bsTy 3 $ mkStaticBuiltin PLC.VerifySignature
        defineBuiltinTerm 'Builtins.verifySignature term [bs, bool]

    -- Error
    do
        -- See Note [Delaying error]
        term <- delayedErrorFunc
        defineBuiltinTerm 'Builtins.error term [unit]

    -- Strings and chars
    do
        let term = mkDynBuiltin PLC.dynamicAppendName
        defineBuiltinTerm 'Builtins.appendString term [str]
    do
        let term = PIR.mkConstant () ("" :: String)
        defineBuiltinTerm 'Builtins.emptyString term [str]
    do
        let term = mkDynBuiltin PLC.dynamicCharToStringName
        defineBuiltinTerm 'Builtins.charToString term [char, str]
    do
        term <- wrapUnitFun strTy $ mkDynBuiltin PLC.dynamicTraceName
        defineBuiltinTerm 'Builtins.trace term [str, unit]

defineBuiltinTypes
    :: Compiling uni m
    => m ()
defineBuiltinTypes = do
    do
        let ty = PLC.toTypeAst $ Proxy @BSL.ByteString
        defineBuiltinType ''Builtins.ByteString ty []
    do
        let ty = PLC.toTypeAst $ Proxy @Integer
        defineBuiltinType ''Integer ty []

    -- Strings and chars
    do
        let ty = PLC.toTypeAst $ Proxy @String
        defineBuiltinType ''Builtins.String ty []
    do
        let ty = PLC.toTypeAst $ Proxy @Char
        defineBuiltinType ''Char ty []

-- | Lookup a builtin term by its TH name. These are assumed to be present, so fails if it cannot find it.
lookupBuiltinTerm :: Compiling uni m => TH.Name -> m (PIRTerm uni)
lookupBuiltinTerm name = do
    ghcName <- GHC.getName <$> getThing name
    maybeTerm <- PIR.lookupTerm () (LexName ghcName)
    case maybeTerm of
        Just t  -> pure t
        Nothing -> throwSd CompilationError $ "Missing builtin definition:" GHC.<+> (GHC.text $ show name)

-- | Lookup a builtin type by its TH name. These are assumed to be present, so fails if it is cannot find it.
lookupBuiltinType :: Compiling uni m => TH.Name -> m (PIRType uni)
lookupBuiltinType name = do
    ghcName <- GHC.getName <$> getThing name
    maybeType <- PIR.lookupType () (LexName ghcName)
    case maybeType of
        Just t  -> pure t
        Nothing -> throwSd CompilationError $ "Missing builtin definition:" GHC.<+> (GHC.text $ show name)

-- | The function 'error :: forall a . a'.
errorFunc :: Compiling uni m => m (PIRTerm uni)
errorFunc = do
    n <- safeFreshTyName "e"
    pure $ PIR.TyAbs () n (PIR.Type ()) (PIR.Error () (PIR.TyVar () n))

-- | The delayed error function 'error :: forall a . () -> a'.
delayedErrorFunc :: Compiling uni m => m (PIRTerm uni)
delayedErrorFunc = do
    n <- safeFreshTyName "e"
    let body = PIR.Error () (PIR.TyVar () n)
    PIR.TyAbs () n (PIR.Type ()) <$> delay body

-- | The type 'forall a. a'.
errorTy :: Compiling uni m => m (PIRType uni)
errorTy = do
    tyname <- safeFreshTyName "a"
    pure $ PIR.TyForall () tyname (PIR.Type ()) (PIR.TyVar () tyname)

-- TODO: bind the converter to a name too. Need an appropriate GHC.Name for
-- it, since that's what our definitions are hung off. Also the type wouldn't
-- be a simple conversion of the Haskell type, because it takes a Scott boolean.
-- | Convert a Scott-encoded Boolean into a Haskell Boolean.
scottBoolToHaskellBool :: Compiling uni m => m (PIRTerm uni)
scottBoolToHaskellBool = do
    let scottBoolTy = Bool.bool
    haskellBoolTy <- compileType GHC.boolTy

    arg <- liftQuote $ freshName "b"
    let instantiatedMatch = PIR.TyInst () (PIR.staticBuiltinNameAsTerm PLC.IfThenElse) haskellBoolTy

    haskellTrue <- compileDataConRef GHC.trueDataCon
    haskellFalse <- compileDataConRef GHC.falseDataCon
    pure $
        PIR.LamAbs () arg scottBoolTy $
        PIR.mkIterApp () instantiatedMatch [ (PIR.Var () arg), haskellTrue, haskellFalse ]

-- | Wrap an relation of arity @n@ that produces a Scott boolean.
wrapRel :: Compiling uni m => PIRType uni -> Int -> PIRTerm uni -> m (PIRTerm uni)
wrapRel argTy arity term = do
    args <- replicateM arity $ do
        name <- safeFreshName "arg"
        pure $ PIR.VarDecl () name argTy

    converter <- scottBoolToHaskellBool

    pure $
        PIR.mkIterLamAbs args $
        PIR.Apply () converter (PIR.mkIterApp () term (fmap (PIR.mkVar ()) args))

-- | Convert a Scott-encoded Unit into a Haskell Unit.
scottUnitToHaskellUnit :: Compiling uni m => m (PIRTerm uni)
scottUnitToHaskellUnit = do
    let scottUnitTy = Unit.unit

    arg <- liftQuote $ freshName "b"

    haskellUnitVal <- compileDataConRef GHC.unitDataCon
    pure $ PIR.LamAbs () arg scottUnitTy haskellUnitVal

-- | Wrap an function with the given argument type that produces a Scott unit.
wrapUnitFun :: Compiling uni m => PIRType uni -> PIRTerm uni -> m (PIRTerm uni)
wrapUnitFun argTy term = do
    arg <- do
        name <- safeFreshName "arg"
        pure $ PIR.VarDecl () name argTy

    converter <- scottUnitToHaskellUnit

    pure $
        PIR.mkIterLamAbs [arg] $
        PIR.Apply () converter (PIR.Apply () term (PIR.mkVar () arg))
