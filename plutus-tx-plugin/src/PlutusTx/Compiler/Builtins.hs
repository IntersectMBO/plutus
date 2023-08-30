-- editorconfig-checker-disable-file
{-# LANGUAGE ConstraintKinds       #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE TemplateHaskellQuotes #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeOperators         #-}

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
import PlutusCore.Crypto.BLS12_381.G1 qualified as BLS12_381.G1
import PlutusCore.Crypto.BLS12_381.G2 qualified as BLS12_381.G2
import PlutusCore.Crypto.BLS12_381.Pairing qualified as BLS12_381.Pairing
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
mkBuiltin = PIR.Builtin annMayInline

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
    , 'Builtins.blake2b_224
    , 'Builtins.blake2b_256
    , 'Builtins.keccak_256
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

    , ''Builtins.BuiltinBLS12_381_G1_Element
    , 'Builtins.bls12_381_G1_equals
    , 'Builtins.bls12_381_G1_add
    , 'Builtins.bls12_381_G1_neg
    , 'Builtins.bls12_381_G1_scalarMul
    , 'Builtins.bls12_381_G1_compress
    , 'Builtins.bls12_381_G1_uncompress
    , 'Builtins.bls12_381_G1_hashToGroup
    , 'Builtins.bls12_381_G1_zero
    , 'Builtins.bls12_381_G1_generator

    , ''Builtins.BuiltinBLS12_381_G2_Element
    , 'Builtins.bls12_381_G2_equals
    , 'Builtins.bls12_381_G2_add
    , 'Builtins.bls12_381_G2_neg
    , 'Builtins.bls12_381_G2_scalarMul
    , 'Builtins.bls12_381_G2_compress
    , 'Builtins.bls12_381_G2_uncompress
    , 'Builtins.bls12_381_G2_hashToGroup
    , 'Builtins.bls12_381_G2_zero
    , 'Builtins.bls12_381_G2_generator

    , ''Builtins.BuiltinBLS12_381_MlResult
    , 'Builtins.bls12_381_millerLoop
    , 'Builtins.bls12_381_mulMlResult
    , 'Builtins.bls12_381_finalVerify
    ]

defineBuiltinTerm :: CompilingDefault uni fun m ann => Ann -> TH.Name -> PIRTerm uni fun -> m ()
defineBuiltinTerm ann name term = do
    ghcId <- GHC.tyThingId <$> getThing name
    var <- compileVarFresh ann ghcId
    semvar <- asks ccBuiltinSemanticsVariant
    -- See Note [Builtin terms and values]
    let strictness = if PIR.isPure semvar (const PIR.NonStrict) term then PIR.Strict else PIR.NonStrict
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
    defineBuiltinTerm annMayInline 'Builtins.ifThenElse $ mkBuiltin PLC.IfThenElse
    defineBuiltinTerm annMayInline 'Builtins.true       $ PIR.mkConstant annMayInline True
    defineBuiltinTerm annMayInline 'Builtins.false      $ PIR.mkConstant annMayInline False

    defineBuiltinTerm annMayInline 'Builtins.unitval    $ PIR.mkConstant annMayInline ()
    defineBuiltinTerm annMayInline 'Builtins.chooseUnit $ mkBuiltin PLC.ChooseUnit

    -- Bytestring builtins
    defineBuiltinTerm annMayInline 'Builtins.appendByteString                $ mkBuiltin PLC.AppendByteString
    defineBuiltinTerm annMayInline 'Builtins.consByteString                  $ mkBuiltin PLC.ConsByteString
    defineBuiltinTerm annMayInline 'Builtins.sliceByteString                 $ mkBuiltin PLC.SliceByteString
    defineBuiltinTerm annMayInline 'Builtins.lengthOfByteString              $ mkBuiltin PLC.LengthOfByteString
    defineBuiltinTerm annMayInline 'Builtins.indexByteString                 $ mkBuiltin PLC.IndexByteString
    defineBuiltinTerm annMayInline 'Builtins.sha2_256                        $ mkBuiltin PLC.Sha2_256
    defineBuiltinTerm annMayInline 'Builtins.sha3_256                        $ mkBuiltin PLC.Sha3_256
    defineBuiltinTerm annMayInline 'Builtins.blake2b_224                     $ mkBuiltin PLC.Blake2b_224
    defineBuiltinTerm annMayInline 'Builtins.blake2b_256                     $ mkBuiltin PLC.Blake2b_256
    defineBuiltinTerm annMayInline 'Builtins.keccak_256                      $ mkBuiltin PLC.Keccak_256
    defineBuiltinTerm annMayInline 'Builtins.equalsByteString                $ mkBuiltin PLC.EqualsByteString
    defineBuiltinTerm annMayInline 'Builtins.lessThanByteString              $ mkBuiltin PLC.LessThanByteString
    defineBuiltinTerm annMayInline 'Builtins.lessThanEqualsByteString        $ mkBuiltin PLC.LessThanEqualsByteString
    defineBuiltinTerm annMayInline 'Builtins.emptyByteString                 $ PIR.mkConstant annMayInline BS.empty
    defineBuiltinTerm annMayInline 'Builtins.decodeUtf8                      $ mkBuiltin PLC.DecodeUtf8
    defineBuiltinTerm annMayInline 'Builtins.verifyEcdsaSecp256k1Signature   $ mkBuiltin PLC.VerifyEcdsaSecp256k1Signature
    defineBuiltinTerm annMayInline 'Builtins.verifySchnorrSecp256k1Signature $ mkBuiltin PLC.VerifySchnorrSecp256k1Signature

    -- Crypto
    defineBuiltinTerm annMayInline 'Builtins.verifyEd25519Signature $ mkBuiltin PLC.VerifyEd25519Signature

    -- Integer builtins
    defineBuiltinTerm annMayInline 'Builtins.addInteger             $ mkBuiltin PLC.AddInteger
    defineBuiltinTerm annMayInline 'Builtins.subtractInteger        $ mkBuiltin PLC.SubtractInteger
    defineBuiltinTerm annMayInline 'Builtins.multiplyInteger        $ mkBuiltin PLC.MultiplyInteger
    defineBuiltinTerm annMayInline 'Builtins.divideInteger          $ mkBuiltin PLC.DivideInteger
    defineBuiltinTerm annMayInline 'Builtins.modInteger             $ mkBuiltin PLC.ModInteger
    defineBuiltinTerm annMayInline 'Builtins.quotientInteger        $ mkBuiltin PLC.QuotientInteger
    defineBuiltinTerm annMayInline 'Builtins.remainderInteger       $ mkBuiltin PLC.RemainderInteger
    defineBuiltinTerm annMayInline 'Builtins.lessThanInteger        $ mkBuiltin PLC.LessThanInteger
    defineBuiltinTerm annMayInline 'Builtins.lessThanEqualsInteger  $ mkBuiltin PLC.LessThanEqualsInteger
    defineBuiltinTerm annMayInline 'Builtins.equalsInteger          $ mkBuiltin PLC.EqualsInteger

    -- Error
    -- See Note [Delaying error]
    func <- delayedErrorFunc
    -- We always want to inline `error :: forall a . () -> a`, hence `annAlwaysInline`.
    defineBuiltinTerm annAlwaysInline 'Builtins.error func

    -- Strings and chars
    defineBuiltinTerm annMayInline 'Builtins.appendString $ mkBuiltin PLC.AppendString
    defineBuiltinTerm annMayInline 'Builtins.emptyString  $ PIR.mkConstant annMayInline ("" :: Text)
    defineBuiltinTerm annMayInline 'Builtins.equalsString $ mkBuiltin PLC.EqualsString
    defineBuiltinTerm annMayInline 'Builtins.encodeUtf8   $ mkBuiltin PLC.EncodeUtf8

    -- Tracing
    -- When `remove-trace` is specified, we define `trace` as `\_ a -> a` instead of the builtin version.
    (traceTerm, ann) <-
        if coRemoveTrace compileOpts
            then liftQuote $ do
                ta <- freshTyName "a"
                t <- freshName "t"
                a <- freshName "a"
                pure
                    ( PIR.tyAbs annMayInline ta (PLC.Type annMayInline) $
                        PIR.mkIterLamAbs
                            [ PIR.VarDecl annMayInline t (PIR.mkTyBuiltin @_ @Text annMayInline)
                            , PIR.VarDecl annMayInline a (PLC.TyVar annMayInline ta)
                            ]
                            $ PIR.Var annMayInline a
                    , annMayInline
                    )
            else pure (mkBuiltin PLC.Trace, annMayInline)
    defineBuiltinTerm ann 'Builtins.trace traceTerm

    -- Pairs
    defineBuiltinTerm annMayInline 'Builtins.fst        $ mkBuiltin PLC.FstPair
    defineBuiltinTerm annMayInline 'Builtins.snd        $ mkBuiltin PLC.SndPair
    defineBuiltinTerm annMayInline 'Builtins.mkPairData $ mkBuiltin PLC.MkPairData

    -- List
    defineBuiltinTerm annMayInline 'Builtins.null          $ mkBuiltin PLC.NullList
    defineBuiltinTerm annMayInline 'Builtins.head          $ mkBuiltin PLC.HeadList
    defineBuiltinTerm annMayInline 'Builtins.tail          $ mkBuiltin PLC.TailList
    defineBuiltinTerm annMayInline 'Builtins.chooseList    $ mkBuiltin PLC.ChooseList
    defineBuiltinTerm annMayInline 'Builtins.mkNilData     $ mkBuiltin PLC.MkNilData
    defineBuiltinTerm annMayInline 'Builtins.mkNilPairData $ mkBuiltin PLC.MkNilPairData
    defineBuiltinTerm annMayInline 'Builtins.mkCons        $ mkBuiltin PLC.MkCons

    -- Data
    defineBuiltinTerm annMayInline 'Builtins.chooseData         $ mkBuiltin PLC.ChooseData
    defineBuiltinTerm annMayInline 'Builtins.equalsData         $ mkBuiltin PLC.EqualsData
    defineBuiltinTerm annMayInline 'Builtins.mkConstr           $ mkBuiltin PLC.ConstrData
    defineBuiltinTerm annMayInline 'Builtins.mkMap              $ mkBuiltin PLC.MapData
    defineBuiltinTerm annMayInline 'Builtins.mkList             $ mkBuiltin PLC.ListData
    defineBuiltinTerm annMayInline 'Builtins.mkI                $ mkBuiltin PLC.IData
    defineBuiltinTerm annMayInline 'Builtins.mkB                $ mkBuiltin PLC.BData
    defineBuiltinTerm annMayInline 'Builtins.unsafeDataAsConstr $ mkBuiltin PLC.UnConstrData
    defineBuiltinTerm annMayInline 'Builtins.unsafeDataAsMap    $ mkBuiltin PLC.UnMapData
    defineBuiltinTerm annMayInline 'Builtins.unsafeDataAsList   $ mkBuiltin PLC.UnListData
    defineBuiltinTerm annMayInline 'Builtins.unsafeDataAsB      $ mkBuiltin PLC.UnBData
    defineBuiltinTerm annMayInline 'Builtins.unsafeDataAsI      $ mkBuiltin PLC.UnIData
    defineBuiltinTerm annMayInline 'Builtins.serialiseData      $ mkBuiltin PLC.SerialiseData

    -- BLS
    defineBuiltinTerm annMayInline 'Builtins.bls12_381_G1_equals      $ mkBuiltin PLC.Bls12_381_G1_equal
    defineBuiltinTerm annMayInline 'Builtins.bls12_381_G1_add         $ mkBuiltin PLC.Bls12_381_G1_add
    defineBuiltinTerm annMayInline 'Builtins.bls12_381_G1_neg         $ mkBuiltin PLC.Bls12_381_G1_neg
    defineBuiltinTerm annMayInline 'Builtins.bls12_381_G1_scalarMul   $ mkBuiltin PLC.Bls12_381_G1_scalarMul
    defineBuiltinTerm annMayInline 'Builtins.bls12_381_G1_compress    $ mkBuiltin PLC.Bls12_381_G1_compress
    defineBuiltinTerm annMayInline 'Builtins.bls12_381_G1_uncompress  $ mkBuiltin PLC.Bls12_381_G1_uncompress
    defineBuiltinTerm annMayInline 'Builtins.bls12_381_G1_hashToGroup $ mkBuiltin PLC.Bls12_381_G1_hashToGroup
    -- The next two constants are both 48 bytes long, so in fact we probably don't want to inline them.
    defineBuiltinTerm annMayInline 'Builtins.bls12_381_G1_zero        $ PIR.mkConstant annMayInline BLS12_381.G1.zero
    defineBuiltinTerm annMayInline 'Builtins.bls12_381_G1_generator   $ PIR.mkConstant annMayInline BLS12_381.G1.generator
    defineBuiltinTerm annMayInline 'Builtins.bls12_381_G2_equals      $ mkBuiltin PLC.Bls12_381_G2_equal
    defineBuiltinTerm annMayInline 'Builtins.bls12_381_G2_add         $ mkBuiltin PLC.Bls12_381_G2_add
    defineBuiltinTerm annMayInline 'Builtins.bls12_381_G2_scalarMul   $ mkBuiltin PLC.Bls12_381_G2_scalarMul
    defineBuiltinTerm annMayInline 'Builtins.bls12_381_G2_neg         $ mkBuiltin PLC.Bls12_381_G2_neg
    defineBuiltinTerm annMayInline 'Builtins.bls12_381_G2_compress    $ mkBuiltin PLC.Bls12_381_G2_compress
    defineBuiltinTerm annMayInline 'Builtins.bls12_381_G2_uncompress  $ mkBuiltin PLC.Bls12_381_G2_uncompress
    defineBuiltinTerm annMayInline 'Builtins.bls12_381_G2_hashToGroup $ mkBuiltin PLC.Bls12_381_G2_hashToGroup
    -- The next two constants are both 96 bytes long, so in fact we probably don't want to inline them.
    defineBuiltinTerm annMayInline 'Builtins.bls12_381_G2_zero        $ PIR.mkConstant annMayInline BLS12_381.G2.zero
    defineBuiltinTerm annMayInline 'Builtins.bls12_381_G2_generator   $ PIR.mkConstant annMayInline BLS12_381.G2.generator
    defineBuiltinTerm annMayInline 'Builtins.bls12_381_millerLoop     $ mkBuiltin PLC.Bls12_381_millerLoop
    defineBuiltinTerm annMayInline 'Builtins.bls12_381_mulMlResult    $ mkBuiltin PLC.Bls12_381_mulMlResult
    defineBuiltinTerm annMayInline 'Builtins.bls12_381_finalVerify    $ mkBuiltin PLC.Bls12_381_finalVerify


defineBuiltinTypes
    :: CompilingDefault uni fun m ann
    => m ()
defineBuiltinTypes = do
    defineBuiltinType ''Builtins.BuiltinByteString . ($> annMayInline) $ PLC.toTypeAst $ Proxy @BS.ByteString
    defineBuiltinType ''Integer . ($> annMayInline) $ PLC.toTypeAst $ Proxy @Integer
    defineBuiltinType ''Builtins.BuiltinBool . ($> annMayInline) $ PLC.toTypeAst $ Proxy @Bool
    defineBuiltinType ''Builtins.BuiltinUnit . ($> annMayInline) $ PLC.toTypeAst $ Proxy @()
    defineBuiltinType ''Builtins.BuiltinString . ($> annMayInline) $ PLC.toTypeAst $ Proxy @Text
    defineBuiltinType ''Builtins.BuiltinData . ($> annMayInline) $ PLC.toTypeAst $ Proxy @PLC.Data
    defineBuiltinType ''Builtins.BuiltinPair . ($> annMayInline) $ PLC.TyBuiltin () (PLC.SomeTypeIn PLC.DefaultUniProtoPair)
    defineBuiltinType ''Builtins.BuiltinList . ($> annMayInline) $ PLC.TyBuiltin () (PLC.SomeTypeIn PLC.DefaultUniProtoList)
    defineBuiltinType ''Builtins.BuiltinBLS12_381_G1_Element . ($> annMayInline) $ PLC.toTypeAst $ Proxy @BLS12_381.G1.Element
    defineBuiltinType ''Builtins.BuiltinBLS12_381_G2_Element . ($> annMayInline) $ PLC.toTypeAst $ Proxy @BLS12_381.G2.Element
    defineBuiltinType ''Builtins.BuiltinBLS12_381_MlResult . ($> annMayInline) $ PLC.toTypeAst $ Proxy @BLS12_381.Pairing.MlResult

-- | Lookup a builtin term by its TH name. These are assumed to be present, so fails if it cannot find it.
lookupBuiltinTerm :: Compiling uni fun m ann => TH.Name -> m (PIRTerm uni fun)
lookupBuiltinTerm name = do
    ghcName <- GHC.getName <$> getThing name
    maybeTerm <- PIR.lookupTerm annMayInline (LexName ghcName)
    case maybeTerm of
        Just t  -> pure t
        Nothing -> throwSd CompilationError $ "Missing builtin definition:" GHC.<+> (GHC.text $ show name)

-- | Lookup a builtin type by its TH name. These are assumed to be present, so fails if it is cannot find it.
lookupBuiltinType :: Compiling uni fun m ann => TH.Name -> m (PIRType uni)
lookupBuiltinType name = do
    ghcName <- GHC.getName <$> getThing name
    maybeType <- PIR.lookupType annMayInline (LexName ghcName)
    case maybeType of
        Just t  -> pure t
        Nothing -> throwSd CompilationError $ "Missing builtin definition:" GHC.<+> (GHC.text $ show name)

-- | The function 'error :: forall a . a'.
errorFunc :: Compiling uni fun m ann => m (PIRTerm uni fun)
errorFunc = do
    n <- safeFreshTyName "e"
    pure $ PIR.TyAbs annMayInline n (PIR.Type annMayInline) (PIR.Error annMayInline (PIR.TyVar annMayInline n))

-- | The delayed error function 'error :: forall a . () -> a'.
delayedErrorFunc :: CompilingDefault uni fun m ann => m (PIRTerm uni fun)
delayedErrorFunc = do
    n <- safeFreshTyName "a"
    t <- liftQuote (freshName "thunk")
    let ty = PLC.toTypeAst $ Proxy @()
    pure $ PIR.TyAbs annMayInline n (PIR.Type annMayInline) $
        PIR.LamAbs annMayInline t (ty $> annMayInline) $ PIR.Error annMayInline (PIR.TyVar annMayInline n)
