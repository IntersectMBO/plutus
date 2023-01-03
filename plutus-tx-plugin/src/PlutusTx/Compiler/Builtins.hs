-- editorconfig-checker-disable-file
{-# LANGUAGE ConstraintKinds   #-}
{-# LANGUAGE DataKinds         #-}
{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell   #-}
{-# LANGUAGE TypeApplications  #-}
{-# LANGUAGE TypeFamilies      #-}
{-# LANGUAGE TypeOperators     #-}

-- | Functions for compiling Plutus Core builtins.
module PlutusTx.Compiler.Builtins (
    builtinNames
    , defineBuiltinTypes
    , defineBuiltinTerms
    , lookupBuiltinTerm
    , lookupBuiltinType
    , errorFunc) where

import PlutusTx.Builtins.Class qualified as Builtins
import PlutusTx.Builtins.Internal qualified as Builtins

import PlutusTx.Compiler.Error
import PlutusTx.Compiler.Names
import PlutusTx.Compiler.Types
import PlutusTx.Compiler.Utils
import PlutusTx.PIRTypes

import PlutusIR qualified as PIR
import PlutusIR.Compiler.Definitions qualified as PIR
import PlutusIR.Compiler.Names
import PlutusIR.MkPir qualified as PIR
import PlutusIR.Purity qualified as PIR

import PlutusCore qualified as PLC
import PlutusCore.Builtin qualified as PLC
import PlutusCore.Data qualified as PLC
import PlutusCore.Quote

import GHC.Plugins qualified as GHC
import GHC.Types.TyThing qualified as GHC

import Language.Haskell.TH.Syntax qualified as TH

import Control.Monad.Reader (ask, asks)

import Data.ByteString qualified as BS
import Data.Functor
import Data.Proxy
import Data.Text (Text)

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

mkBuiltin :: fun -> PIR.Term tyname name uni fun Ann
mkBuiltin = PIR.Builtin AnnOther

-- | The 'TH.Name's for which 'NameInfo' needs to be provided.
builtinNames :: [TH.Name]
builtinNames = [
      ''Builtins.BuiltinByteString
    , 'Builtins.appendByteString
    , 'Builtins.consByteString
    , 'Builtins.sliceByteString
    , 'Builtins.lengthOfByteString
    , 'Builtins.indexByteString
    , 'Builtins.sha2_256
    , 'Builtins.sha3_256
    , 'Builtins.blake2b_256
    , 'Builtins.equalsByteString
    , 'Builtins.lessThanByteString
    , 'Builtins.lessThanEqualsByteString
    , 'Builtins.emptyByteString
    , 'Builtins.decodeUtf8
    , 'Builtins.stringToBuiltinByteString
    , 'Builtins.verifyEcdsaSecp256k1Signature
    , 'Builtins.verifySchnorrSecp256k1Signature

    , 'Builtins.verifyEd25519Signature

    , ''Integer
    , 'Builtins.addInteger
    , 'Builtins.subtractInteger
    , 'Builtins.multiplyInteger
    , 'Builtins.divideInteger
    , 'Builtins.modInteger
    , 'Builtins.quotientInteger
    , 'Builtins.remainderInteger
    , 'Builtins.lessThanInteger
    , 'Builtins.lessThanEqualsInteger
    , 'Builtins.equalsInteger

    , 'Builtins.error

    , ''Builtins.BuiltinString
    , 'Builtins.appendString
    , 'Builtins.emptyString
    , 'Builtins.equalsString
    , 'Builtins.encodeUtf8
    -- This one is special
    , 'Builtins.stringToBuiltinString

    , 'Builtins.trace

    , ''Builtins.BuiltinBool
    , 'Builtins.ifThenElse
    , 'Builtins.true
    , 'Builtins.false

    , ''Builtins.BuiltinUnit
    , 'Builtins.unitval
    , 'Builtins.chooseUnit

    , ''Builtins.BuiltinPair
    , 'Builtins.fst
    , 'Builtins.snd
    , 'Builtins.mkPairData

    , ''Builtins.BuiltinList
    , 'Builtins.null
    , 'Builtins.head
    , 'Builtins.tail
    , 'Builtins.chooseList
    , 'Builtins.mkNilData
    , 'Builtins.mkNilPairData
    , 'Builtins.mkCons

    , ''Builtins.BuiltinData
    , 'Builtins.chooseData
    , 'Builtins.equalsData
    , 'Builtins.serialiseData
    , 'Builtins.mkConstr
    , 'Builtins.mkMap
    , 'Builtins.mkList
    , 'Builtins.mkI
    , 'Builtins.mkB
    , 'Builtins.unsafeDataAsConstr
    , 'Builtins.unsafeDataAsMap
    , 'Builtins.unsafeDataAsList
    , 'Builtins.unsafeDataAsB
    , 'Builtins.unsafeDataAsI
    ]

defineBuiltinTerm :: CompilingDefault uni fun m ann => Ann -> TH.Name -> PIRTerm uni fun -> m ()
defineBuiltinTerm ann name term = do
    ghcId <- GHC.tyThingId <$> getThing name
    var <- compileVarFresh ann ghcId
    ver <- asks ccBuiltinVer
    -- See Note [Builtin terms and values]
    let strictness = if PIR.isPure ver (const PIR.NonStrict) term then PIR.Strict else PIR.NonStrict
        def = PIR.Def var (term, strictness)
    PIR.defineTerm (LexName $ GHC.getName ghcId) def mempty

-- | Add definitions for all the builtin types to the environment.
defineBuiltinType :: forall uni fun m ann. Compiling uni fun m ann => TH.Name -> PIRType uni -> m ()
defineBuiltinType name ty = do
    tc <- GHC.tyThingTyCon <$> getThing name
    var <- compileTcTyVarFresh tc
    PIR.defineType (LexName $ GHC.getName tc) (PIR.Def var ty) mempty
    -- these are all aliases for now
    PIR.recordAlias (LexName $ GHC.getName tc)

-- | Add definitions for all the builtin terms to the environment.
defineBuiltinTerms :: CompilingDefault uni fun m ann => m ()
defineBuiltinTerms = do
    CompileContext {ccOpts=compileOpts} <- ask

    -- See Note [Builtin terms and values]
    -- Bool
    defineBuiltinTerm AnnOther 'Builtins.ifThenElse $ mkBuiltin PLC.IfThenElse
    defineBuiltinTerm AnnOther 'Builtins.true $ PIR.mkConstant AnnOther True
    defineBuiltinTerm AnnOther 'Builtins.false $ PIR.mkConstant AnnOther False

    defineBuiltinTerm AnnOther 'Builtins.unitval $ PIR.mkConstant AnnOther ()
    defineBuiltinTerm AnnOther 'Builtins.chooseUnit $ mkBuiltin PLC.ChooseUnit

    -- Bytestring builtins
    defineBuiltinTerm AnnOther 'Builtins.appendByteString $ mkBuiltin PLC.AppendByteString
    defineBuiltinTerm AnnOther 'Builtins.consByteString $ mkBuiltin PLC.ConsByteString
    defineBuiltinTerm AnnOther 'Builtins.sliceByteString $ mkBuiltin PLC.SliceByteString
    defineBuiltinTerm AnnOther 'Builtins.lengthOfByteString $ mkBuiltin PLC.LengthOfByteString
    defineBuiltinTerm AnnOther 'Builtins.indexByteString $ mkBuiltin PLC.IndexByteString
    defineBuiltinTerm AnnOther 'Builtins.sha2_256 $ mkBuiltin PLC.Sha2_256
    defineBuiltinTerm AnnOther 'Builtins.sha3_256 $ mkBuiltin PLC.Sha3_256
    defineBuiltinTerm AnnOther 'Builtins.blake2b_256 $ mkBuiltin PLC.Blake2b_256
    defineBuiltinTerm AnnOther 'Builtins.equalsByteString $ mkBuiltin PLC.EqualsByteString
    defineBuiltinTerm AnnOther 'Builtins.lessThanByteString $ mkBuiltin PLC.LessThanByteString
    defineBuiltinTerm AnnOther 'Builtins.lessThanEqualsByteString $ mkBuiltin PLC.LessThanEqualsByteString
    defineBuiltinTerm AnnOther 'Builtins.emptyByteString $ PIR.mkConstant AnnOther BS.empty
    defineBuiltinTerm AnnOther 'Builtins.decodeUtf8 $ mkBuiltin PLC.DecodeUtf8
    defineBuiltinTerm AnnOther 'Builtins.verifyEcdsaSecp256k1Signature $ mkBuiltin PLC.VerifyEcdsaSecp256k1Signature
    defineBuiltinTerm AnnOther 'Builtins.verifySchnorrSecp256k1Signature $ mkBuiltin PLC.VerifySchnorrSecp256k1Signature

    -- Crypto
    defineBuiltinTerm AnnOther 'Builtins.verifyEd25519Signature $ mkBuiltin PLC.VerifyEd25519Signature

    -- Integer builtins
    defineBuiltinTerm AnnOther 'Builtins.addInteger $ mkBuiltin PLC.AddInteger
    defineBuiltinTerm AnnOther 'Builtins.subtractInteger $ mkBuiltin PLC.SubtractInteger
    defineBuiltinTerm AnnOther 'Builtins.multiplyInteger $ mkBuiltin PLC.MultiplyInteger
    defineBuiltinTerm AnnOther 'Builtins.divideInteger $ mkBuiltin PLC.DivideInteger
    defineBuiltinTerm AnnOther 'Builtins.modInteger $ mkBuiltin PLC.ModInteger
    defineBuiltinTerm AnnOther 'Builtins.quotientInteger $ mkBuiltin PLC.QuotientInteger
    defineBuiltinTerm AnnOther 'Builtins.remainderInteger $ mkBuiltin PLC.RemainderInteger
    defineBuiltinTerm AnnOther 'Builtins.lessThanInteger $ mkBuiltin PLC.LessThanInteger
    defineBuiltinTerm AnnOther 'Builtins.lessThanEqualsInteger $ mkBuiltin PLC.LessThanEqualsInteger
    defineBuiltinTerm AnnOther 'Builtins.equalsInteger $ mkBuiltin PLC.EqualsInteger

    -- Error
    -- See Note [Delaying error]
    func <- delayedErrorFunc
    -- We always want to inline `error :: forall a . () -> a`, hence `AnnInline`.
    defineBuiltinTerm AnnInline 'Builtins.error func

    -- Strings and chars
    defineBuiltinTerm AnnOther 'Builtins.appendString $ mkBuiltin PLC.AppendString
    defineBuiltinTerm AnnOther 'Builtins.emptyString $ PIR.mkConstant AnnOther ("" :: Text)
    defineBuiltinTerm AnnOther 'Builtins.equalsString $ mkBuiltin PLC.EqualsString
    defineBuiltinTerm AnnOther 'Builtins.encodeUtf8 $ mkBuiltin PLC.EncodeUtf8

    -- Tracing
    -- When `remove-trace` is specified, we define `trace` as `\_ a -> a` instead of the builtin version.
    (traceTerm, ann) <-
        if coRemoveTrace compileOpts
            then liftQuote $ do
                ta <- freshTyName "a"
                t <- freshName "t"
                a <- freshName "a"
                pure
                    ( PIR.tyAbs AnnOther ta (PLC.Type AnnOther) $
                        PIR.mkIterLamAbs
                            [ PIR.VarDecl AnnOther t (PIR.mkTyBuiltin @_ @Text AnnOther)
                            , PIR.VarDecl AnnOther a (PLC.TyVar AnnOther ta)
                            ]
                            $ PIR.Var AnnOther a
                    , -- We always want to inline `\_ a -> a` (especially because the first
                      -- element is a string), hence `AnnInline`.
                      AnnInline
                    )
            else pure (mkBuiltin PLC.Trace, AnnOther)
    defineBuiltinTerm ann 'Builtins.trace traceTerm

    -- Pairs
    defineBuiltinTerm AnnOther 'Builtins.fst $ mkBuiltin PLC.FstPair
    defineBuiltinTerm AnnOther 'Builtins.snd $ mkBuiltin PLC.SndPair
    defineBuiltinTerm AnnOther 'Builtins.mkPairData $ mkBuiltin PLC.MkPairData

    -- List
    defineBuiltinTerm AnnOther 'Builtins.null $ mkBuiltin PLC.NullList
    defineBuiltinTerm AnnOther 'Builtins.head $ mkBuiltin PLC.HeadList
    defineBuiltinTerm AnnOther 'Builtins.tail $ mkBuiltin PLC.TailList
    defineBuiltinTerm AnnOther 'Builtins.chooseList $ mkBuiltin PLC.ChooseList
    defineBuiltinTerm AnnOther 'Builtins.mkNilData $ mkBuiltin PLC.MkNilData
    defineBuiltinTerm AnnOther 'Builtins.mkNilPairData $ mkBuiltin PLC.MkNilPairData
    defineBuiltinTerm AnnOther 'Builtins.mkCons $ mkBuiltin PLC.MkCons

    -- Data
    defineBuiltinTerm AnnOther 'Builtins.chooseData $ mkBuiltin PLC.ChooseData
    defineBuiltinTerm AnnOther 'Builtins.equalsData $ mkBuiltin PLC.EqualsData
    defineBuiltinTerm AnnOther 'Builtins.mkConstr $ mkBuiltin PLC.ConstrData
    defineBuiltinTerm AnnOther 'Builtins.mkMap $ mkBuiltin PLC.MapData
    defineBuiltinTerm AnnOther 'Builtins.mkList $ mkBuiltin PLC.ListData
    defineBuiltinTerm AnnOther 'Builtins.mkI $ mkBuiltin PLC.IData
    defineBuiltinTerm AnnOther 'Builtins.mkB $ mkBuiltin PLC.BData
    defineBuiltinTerm AnnOther 'Builtins.unsafeDataAsConstr $ mkBuiltin PLC.UnConstrData
    defineBuiltinTerm AnnOther 'Builtins.unsafeDataAsMap $ mkBuiltin PLC.UnMapData
    defineBuiltinTerm AnnOther 'Builtins.unsafeDataAsList $ mkBuiltin PLC.UnListData
    defineBuiltinTerm AnnOther 'Builtins.unsafeDataAsB $ mkBuiltin PLC.UnBData
    defineBuiltinTerm AnnOther 'Builtins.unsafeDataAsI $ mkBuiltin PLC.UnIData
    defineBuiltinTerm AnnOther 'Builtins.serialiseData $ mkBuiltin PLC.SerialiseData

defineBuiltinTypes
    :: CompilingDefault uni fun m ann
    => m ()
defineBuiltinTypes = do
    defineBuiltinType ''Builtins.BuiltinByteString . ($> AnnOther) $ PLC.toTypeAst $ Proxy @BS.ByteString
    defineBuiltinType ''Integer . ($> AnnOther) $ PLC.toTypeAst $ Proxy @Integer
    defineBuiltinType ''Builtins.BuiltinBool . ($> AnnOther) $ PLC.toTypeAst $ Proxy @Bool
    defineBuiltinType ''Builtins.BuiltinUnit . ($> AnnOther) $ PLC.toTypeAst $ Proxy @()
    defineBuiltinType ''Builtins.BuiltinString . ($> AnnOther) $ PLC.toTypeAst $ Proxy @Text
    defineBuiltinType ''Builtins.BuiltinData . ($> AnnOther) $ PLC.toTypeAst $ Proxy @PLC.Data
    defineBuiltinType ''Builtins.BuiltinPair . ($> AnnOther) $ PLC.TyBuiltin () (PLC.SomeTypeIn PLC.DefaultUniProtoPair)
    defineBuiltinType ''Builtins.BuiltinList . ($> AnnOther) $ PLC.TyBuiltin () (PLC.SomeTypeIn PLC.DefaultUniProtoList)

-- | Lookup a builtin term by its TH name. These are assumed to be present, so fails if it cannot find it.
lookupBuiltinTerm :: Compiling uni fun m ann => TH.Name -> m (PIRTerm uni fun)
lookupBuiltinTerm name = do
    ghcName <- GHC.getName <$> getThing name
    maybeTerm <- PIR.lookupTerm AnnOther (LexName ghcName)
    case maybeTerm of
        Just t  -> pure t
        Nothing -> throwSd CompilationError $ "Missing builtin definition:" GHC.<+> (GHC.text $ show name)

-- | Lookup a builtin type by its TH name. These are assumed to be present, so fails if it is cannot find it.
lookupBuiltinType :: Compiling uni fun m ann => TH.Name -> m (PIRType uni)
lookupBuiltinType name = do
    ghcName <- GHC.getName <$> getThing name
    maybeType <- PIR.lookupType AnnOther (LexName ghcName)
    case maybeType of
        Just t  -> pure t
        Nothing -> throwSd CompilationError $ "Missing builtin definition:" GHC.<+> (GHC.text $ show name)

-- | The function 'error :: forall a . a'.
errorFunc :: Compiling uni fun m ann => m (PIRTerm uni fun)
errorFunc = do
    n <- safeFreshTyName "e"
    pure $ PIR.TyAbs AnnOther n (PIR.Type AnnOther) (PIR.Error AnnOther (PIR.TyVar AnnOther n))

-- | The delayed error function 'error :: forall a . () -> a'.
delayedErrorFunc :: CompilingDefault uni fun m ann => m (PIRTerm uni fun)
delayedErrorFunc = do
    n <- safeFreshTyName "a"
    t <- liftQuote (freshName "thunk")
    let ty = PLC.toTypeAst $ Proxy @()
    pure $ PIR.TyAbs AnnOther n (PIR.Type AnnOther) $
        PIR.LamAbs AnnOther t (ty $> AnnOther) $ PIR.Error AnnOther (PIR.TyVar AnnOther n)
