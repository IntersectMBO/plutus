{-# LANGUAGE ConstraintKinds   #-}
{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell   #-}
{-# LANGUAGE ViewPatterns      #-}

-- | Functions for compiling Plutus Core builtins.
module Language.Plutus.CoreToPLC.Compiler.Builtins (
    builtinNames
    , defineBuiltinTypes
    , defineBuiltinTerms
    , lookupBuiltinTerm
    , lookupBuiltinType
    , errorTy
    , errorFunc) where

import qualified Language.Plutus.CoreToPLC.Builtins                  as Builtins
import           Language.Plutus.CoreToPLC.Compiler.Definitions
import {-# SOURCE #-} Language.Plutus.CoreToPLC.Compiler.Expr
import           Language.Plutus.CoreToPLC.Compiler.Names
import {-# SOURCE #-} Language.Plutus.CoreToPLC.Compiler.Type
import           Language.Plutus.CoreToPLC.Compiler.Types
import           Language.Plutus.CoreToPLC.Compiler.Utils
import           Language.Plutus.CoreToPLC.Compiler.ValueRestriction
import           Language.Plutus.CoreToPLC.Error
import           Language.Plutus.CoreToPLC.PIRTypes
import           Language.Plutus.CoreToPLC.Utils

import qualified Language.PlutusIR                                   as PIR
import qualified Language.PlutusIR.MkPir                             as PIR

import qualified Language.PlutusCore                                 as PLC
import           Language.PlutusCore.Quote
import qualified Language.PlutusCore.StdLib.Data.Bool                as Bool

import qualified GhcPlugins                                          as GHC

import qualified Language.Haskell.TH.Syntax                          as TH

import           Control.Monad
import           Control.Monad.Reader

import qualified Data.ByteString.Lazy                                as BSL
import qualified Data.Map                                            as Map

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
Haskell. But there is a problem: they use either primitive or Scott-encoded versions of these types,
whereas when we compile them from Haskell they will end up as abstract types, and so the types
won't line up at the call site.

That is, we generate something like this:
(/\ (Int :: *) .
  (\ addInteger : Int -> Int -> Int .
      <use addInteger>
  )
  (\ x,y : Int . <builtin addInteger> x y) -- Uh oh, type error, can't show that Int = <builtin int>!
)
{<builtin int>}

We handle this in two different ways:
- For the types like Bool and Unit which are really algebraic types, and which have constructors etc.
that we care about elsewhere, we insert adaptor code into the definition of the builtin (see note [Mapping builtins]).
- For types like Int and Bytestring which don't have visible constructors, we can treat them as completely opaque,
and we use a transparent type alias. (Actually we fake the alias by actually just substituting the definition in
everywhere until we have aliases in PIR. Bear this in mind for the examples below.)

Here's how that looks for a primitive that takes Ints and returns a Boolean, assuming we have bound Int and Bool
already as an alias and an abstract type respectively:
(\ equalsInteger : Int -> Int -> Bool .
  <use equalsInteger>
)
(\ x, y : Int . -- No need to do anything to the arguments, since we're using a transparent alias for Int
  (<builtin equalsInteger> x y) {Bool} True False -- Immediately match the builtin bool into an abstract Bool
)

We *could* do something like the interleaved definitions that we do for datatypes in PIR. Morally this is perhaps the
right thing to do: we should think of Int and its builtins as a "module" that goes together and where all the definitions
have access to the internals of the other definitions. A datatype definition is then a special case of a module definition.
However, for the moment this would be quite a bit more design work and so we leave it for future work.

For an example of how the "abstract module" approach would look:
(/\ (Int :: *) .
  (\ addInteger : Int -> Int -> Int . -- Type signature is fine inside the abstraction
      <use addInteger>
  )
)
{<builtin int>}
(\ x,y : <builtin int> . <builtin addInteger> x y) -- No type error any more, abstraction is gone
-}

-- | The 'TH.Name's for which 'BuiltinNameInfo' needs to be provided.
builtinNames :: [TH.Name]
builtinNames = [
    ''BSL.ByteString
    , ''Int
    , ''Bool
    , ''()

    , 'Builtins.concatenate
    , 'Builtins.takeByteString
    , 'Builtins.dropByteString
    , 'Builtins.sha2_256
    , 'Builtins.sha3_256
    , 'Builtins.equalsByteString

    , 'Builtins.verifySignature
    , 'Builtins.txhash
    , 'Builtins.blocknum

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
    ]

-- | Get the 'GHC.TyThing' for a given 'TH.Name' which was stored in the builtin name info,
-- failing if it is missing.
getThing :: Converting m => TH.Name -> m GHC.TyThing
getThing name = do
    ConvertingContext{ccBuiltinNameInfo=names} <- ask
    case Map.lookup name names of
        Nothing    -> throwSd ConversionError $ "Missing builtin name:" GHC.<+> (GHC.text $ show name)
        Just thing -> pure thing

defineBuiltinTerm :: Converting m => TH.Name -> PIRTerm -> [GHC.Name] -> m ()
defineBuiltinTerm name term deps = do
    ghcId <- GHC.tyThingId <$> getThing name
    var <- convVarFresh ghcId
    defineTerm (GHC.getName ghcId) (PIR.TermBind () var term) deps

-- | Add definitions for all the builtin types to the environment.
defineBuiltinType :: Converting m => TH.Name -> PIRType -> [GHC.Name] -> m ()
defineBuiltinType name ty deps = do
    tc <- GHC.tyThingTyCon <$> getThing name
    var <- convTcTyVarFresh tc
    defineType (GHC.getName tc) (PIR.TypeBind () var ty) deps
    -- these are all aliases for now
    recordAlias (GHC.getName tc)

-- | Add definitions for all the builtin terms to the environment.
defineBuiltinTerms :: Converting m => m ()
defineBuiltinTerms = do
    bs <- GHC.getName <$> getThing ''BSL.ByteString
    int <- GHC.getName <$> getThing ''Int
    bool <- GHC.getName <$> getThing ''Bool
    unit <- GHC.getName <$> getThing ''()

    -- Bytestring builtins
    do
        let term = instSize haskellBSSize $ mkBuiltin PLC.Concatenate
        defineBuiltinTerm 'Builtins.concatenate term [bs]
    do
        let term = instSize haskellBSSize $ instSize haskellIntSize $ mkBuiltin PLC.TakeByteString
        defineBuiltinTerm 'Builtins.takeByteString term [int, bs]
    do
        let term = instSize haskellBSSize $ instSize haskellIntSize $ mkBuiltin PLC.DropByteString
        defineBuiltinTerm 'Builtins.dropByteString term [int, bs]
    do
        let term = instSize haskellBSSize $ mkBuiltin PLC.SHA2
        defineBuiltinTerm 'Builtins.sha2_256 term [bs]
    do
        let term = instSize haskellBSSize $ mkBuiltin PLC.SHA3
        defineBuiltinTerm 'Builtins.sha3_256 term [bs]
    do
        term <- mkBsRel PLC.EqByteString
        defineBuiltinTerm 'Builtins.equalsByteString term [bs, bool]

    -- Integer builtins
    do
        let term = mkIntFun PLC.AddInteger
        defineBuiltinTerm 'Builtins.addInteger term [int]
    do
        let term = mkIntFun PLC.SubtractInteger
        defineBuiltinTerm 'Builtins.subtractInteger term [int]
    do
        let term = mkIntFun PLC.MultiplyInteger
        defineBuiltinTerm 'Builtins.multiplyInteger term [int]
    do
        let term = mkIntFun PLC.DivideInteger
        defineBuiltinTerm 'Builtins.divideInteger term [int]
    do
        let term = mkIntFun PLC.RemainderInteger
        defineBuiltinTerm 'Builtins.remainderInteger term [int]
    do
        term <- mkIntRel PLC.GreaterThanInteger
        defineBuiltinTerm 'Builtins.greaterThanInteger term [int, bool]
    do
        term <- mkIntRel PLC.GreaterThanEqInteger
        defineBuiltinTerm 'Builtins.greaterThanEqInteger term [int, bool]
    do
        term <- mkIntRel PLC.LessThanInteger
        defineBuiltinTerm 'Builtins.lessThanInteger term [int, bool]
    do
        term <- mkIntRel PLC.LessThanEqInteger
        defineBuiltinTerm 'Builtins.lessThanEqInteger term [int, bool]
    do
        term <- mkIntRel PLC.EqInteger
        defineBuiltinTerm 'Builtins.equalsInteger term [int, bool]

    -- Blockchain builtins
    do
        let term = mkBuiltin PLC.TxHash
        defineBuiltinTerm 'Builtins.txhash term [bs]
    do
        term <- wrapBsRel 3 $ instSize haskellBSSize $ instSize haskellBSSize $ instSize haskellBSSize $ mkBuiltin PLC.VerifySignature
        defineBuiltinTerm 'Builtins.verifySignature term [bs, bool]
    -- TODO: blocknum, this is annoying because we want to actually apply it to a size, which currently crashes in the evaluator
    -- as it's unimplemented

    -- Error
    do
        term <- errorFunc
        defineBuiltinTerm 'Builtins.error term [unit]

defineBuiltinTypes :: Converting m => m ()
defineBuiltinTypes = do
    do
        let ty = appSize haskellBSSize $ PLC.TyBuiltin () PLC.TyByteString
        defineBuiltinType ''BSL.ByteString ty []
    do
        let ty = appSize haskellIntSize (PLC.TyBuiltin () PLC.TyInteger)
        defineBuiltinType ''Int ty []

-- | Lookup a builtin term by its TH name. These are assumed to be present, so fails if it cannot find it.
lookupBuiltinTerm :: Converting m => TH.Name -> m PIRTerm
lookupBuiltinTerm name = do
    ghcName <- GHC.getName <$> getThing name
    maybeTerm <- lookupTermDef ghcName
    case maybeTerm of
        Just t  -> pure t
        Nothing -> throwSd ConversionError $ "Missing builtin definition:" GHC.<+> (GHC.text $ show name)

-- | Lookup a builtin type by its TH name. These are assumed to be present, so fails if it is cannot find it.
lookupBuiltinType :: Converting m => TH.Name -> m PIRType
lookupBuiltinType name = do
    ghcName <- GHC.getName <$> getThing name
    maybeType <- lookupTypeDef ghcName
    case maybeType of
        Just t  -> pure t
        Nothing -> throwSd ConversionError $ "Missing builtin definition:" GHC.<+> (GHC.text $ show name)

-- | The function 'error :: forall a . () -> a'.
errorFunc :: Converting m => m PIRTerm
errorFunc = do
    n <- liftQuote $ freshTyName () "e"
    -- see Note [Value restriction]
    mangleTyAbs $ PIR.TyAbs () n (PIR.Type ()) (PIR.Error () (PIR.TyVar () n))

-- | The type 'forall a. () -> a'.
errorTy :: Converting m => m PIRType
errorTy = do
    tyname <- safeFreshTyName "a"
    mangleTyForall $ PIR.TyForall () tyname (PIR.Type ()) (PIR.TyVar () tyname)

-- TODO: bind the converter to a name too. Need an appropriate GHC.Name for
-- it, since that's what our definitions are hung off. Also the type wouldn't
-- be a simple conversion of the Haskell type, because it takes a Scott boolean.
-- | Convert a Scott-encoded Boolean into a Haskell Boolean.
scottBoolToHaskellBool :: Converting m => m PIRTerm
scottBoolToHaskellBool = do
    scottBoolTy <- liftQuote Bool.getBuiltinBool
    haskellBoolTy <- convType GHC.boolTy

    arg <- liftQuote $ freshName () "b"
    let match = PIR.Var () arg
    let instantiatedMatch = PIR.TyInst () match haskellBoolTy

    haskellTrue <- convDataConRef GHC.trueDataCon
    haskellFalse <- convDataConRef GHC.falseDataCon
    pure $
        PIR.LamAbs () arg scottBoolTy $
        PIR.mkIterApp () instantiatedMatch [ haskellTrue, haskellFalse ]

-- | Wrap an integer relation of arity @n@ that produces a Scott boolean.
wrapIntRel :: Converting m => Int -> PIRTerm -> m PIRTerm
wrapIntRel arity term = do
    intTy <- lookupBuiltinType ''Int
    args <- replicateM arity $ do
        name <- liftQuote $ freshName () "arg"
        pure $ PIR.VarDecl () name intTy

    -- TODO: bind the converter to a name too
    converter <- scottBoolToHaskellBool

    pure $
        PIR.mkIterLamAbs () args $
        PIR.Apply () converter (PIR.mkIterApp () term (fmap (PIR.mkVar ()) args))

mkIntRel :: Converting m => PLC.BuiltinName -> m PIRTerm
mkIntRel name = wrapIntRel 2 $ instSize haskellIntSize (mkBuiltin name)

-- | Wrap an bytestring relation of arity @n@ that produces a Scott boolean.
wrapBsRel :: Converting m => Int -> PIRTerm -> m PIRTerm
wrapBsRel arity term = do
    bsTy <- lookupBuiltinType ''BSL.ByteString
    args <- replicateM arity $ do
        name <- liftQuote $ freshName () "arg"
        pure $ PIR.VarDecl () name bsTy

    converter <- scottBoolToHaskellBool

    pure $
        PIR.mkIterLamAbs () args $
        PIR.Apply () converter (PIR.mkIterApp () term (fmap (PIR.mkVar ()) args))

mkBsRel :: Converting m => PLC.BuiltinName -> m PIRTerm
mkBsRel name = wrapBsRel 2 $ instSize haskellBSSize (mkBuiltin name)
