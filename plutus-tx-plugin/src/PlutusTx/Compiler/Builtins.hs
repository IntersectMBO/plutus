-- editorconfig-checker-disable-file
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskellQuotes #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

-- | Functions for compiling Plutus Core builtins.
module PlutusTx.Compiler.Builtins
  ( builtinNames
  , defineBuiltinTypes
  , defineBuiltinTerms
  , defineBoolType
  , lookupBuiltinTerm
  , lookupBuiltinType
  , errorFunc
  ) where

import PlutusTx.Builtins.HasOpaque qualified as Builtins
import PlutusTx.Builtins.Internal qualified as Builtins

import PlutusTx.Compiler.Error
import PlutusTx.Compiler.Names
import PlutusTx.Compiler.Types
import PlutusTx.Compiler.Utils
import PlutusTx.PIRTypes

import PlutusIR qualified as PIR
import PlutusIR.Compiler.Definitions qualified as PIR
import PlutusIR.Compiler.Names
import PlutusIR.Compiler.Types qualified as PIR
import PlutusIR.MkPir qualified as PIR
import PlutusIR.Purity qualified as PIR

import PlutusCore qualified as PLC
import PlutusCore.Builtin qualified as PLC
import PlutusCore.Crypto.BLS12_381.G1 qualified as BLS12_381.G1
import PlutusCore.Crypto.BLS12_381.G2 qualified as BLS12_381.G2
import PlutusCore.Crypto.BLS12_381.Pairing qualified as BLS12_381.Pairing
import PlutusCore.Data qualified as PLC
import PlutusCore.Quote
import PlutusCore.Value (Value)

import GHC.Plugins qualified as GHC

import Language.Haskell.TH.Syntax qualified as TH

import Control.Monad.Reader (asks)

import Data.ByteString qualified as BS
import Data.Functor
import Data.Proxy
import Data.Set qualified as Set
import Data.Text (Text)
import PlutusPrelude (enumerate, for_)

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
that we care about elsewhere, we insert adaptor code into the definition of the builtin (see Note [Mapping builtins]).
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
builtinNames =
  [ ''Builtins.BuiltinByteString
  , ''Builtins.BuiltinByteStringHex
  , ''Builtins.BuiltinByteStringUtf8
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
  , 'Builtins.ripemd_160
  , 'Builtins.equalsByteString
  , 'Builtins.lessThanByteString
  , 'Builtins.lessThanEqualsByteString
  , 'Builtins.emptyByteString
  , 'Builtins.decodeUtf8
  , 'Builtins.stringToBuiltinByteString
  , 'Builtins.stringToBuiltinByteStringHex
  , 'Builtins.stringToBuiltinByteStringUtf8
  , 'Builtins.verifyEcdsaSecp256k1Signature
  , 'Builtins.verifySchnorrSecp256k1Signature
  , 'Builtins.verifyEd25519Signature
  , ''Builtins.BuiltinInteger
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
  , 'Builtins.caseInteger
  , 'Builtins.error
  , ''Builtins.BuiltinString
  , 'Builtins.appendString
  , 'Builtins.emptyString
  , 'Builtins.equalsString
  , 'Builtins.encodeUtf8
  , 'Builtins.integerToByteString
  , 'Builtins.byteStringToInteger
  , -- This one is special
    'Builtins.stringToBuiltinString
  , 'Builtins.trace
  , 'Builtins.ifThenElse
  , ''Builtins.BuiltinUnit
  , 'Builtins.unitval
  , 'Builtins.chooseUnit
  , ''Builtins.BuiltinPair
  , 'Builtins.fst
  , 'Builtins.snd
  , 'Builtins.casePair
  , 'Builtins.mkPairData
  , ''Builtins.BuiltinList
  , 'Builtins.null
  , 'Builtins.head
  , 'Builtins.tail
  , 'Builtins.chooseList
  , 'Builtins.caseList'
  , 'Builtins.mkNilData
  , 'Builtins.mkNilPairData
  , 'Builtins.mkCons
  , 'Builtins.drop
  , ''Builtins.BuiltinArray
  , 'Builtins.lengthOfArray
  , 'Builtins.listToArray
  , 'Builtins.indexArray
  , ''Builtins.BuiltinData
  , 'Builtins.chooseData
  , 'Builtins.equalsData
  , 'Builtins.serialiseData
  , 'Builtins.mkConstr
  , 'Builtins.mkMap
  , 'Builtins.mkList
  , 'Builtins.mkArray
  , 'Builtins.mkI
  , 'Builtins.mkB
  , 'Builtins.unsafeDataAsConstr
  , 'Builtins.unsafeDataAsMap
  , 'Builtins.unsafeDataAsList
  , 'Builtins.unsafeDataAsArray
  , 'Builtins.unsafeDataAsB
  , 'Builtins.unsafeDataAsI
  , ''Builtins.BuiltinBLS12_381_G1_Element
  , 'Builtins.bls12_381_G1_equals
  , 'Builtins.bls12_381_G1_add
  , 'Builtins.bls12_381_G1_neg
  , 'Builtins.bls12_381_G1_scalarMul
  , 'Builtins.bls12_381_G1_multiScalarMul
  , 'Builtins.bls12_381_G1_compress
  , 'Builtins.bls12_381_G1_uncompress
  , 'Builtins.bls12_381_G1_hashToGroup
  , 'Builtins.bls12_381_G1_compressed_zero
  , 'Builtins.bls12_381_G1_compressed_generator
  , ''Builtins.BuiltinBLS12_381_G2_Element
  , 'Builtins.bls12_381_G2_equals
  , 'Builtins.bls12_381_G2_add
  , 'Builtins.bls12_381_G2_neg
  , 'Builtins.bls12_381_G2_scalarMul
  , 'Builtins.bls12_381_G2_multiScalarMul
  , 'Builtins.bls12_381_G2_compress
  , 'Builtins.bls12_381_G2_uncompress
  , 'Builtins.bls12_381_G2_hashToGroup
  , 'Builtins.bls12_381_G2_compressed_zero
  , 'Builtins.bls12_381_G2_compressed_generator
  , ''Builtins.BuiltinBLS12_381_MlResult
  , 'Builtins.bls12_381_millerLoop
  , 'Builtins.bls12_381_mulMlResult
  , 'Builtins.bls12_381_finalVerify
  , 'Builtins.integerToByteString
  , 'Builtins.byteStringToInteger
  , 'Builtins.andByteString
  , 'Builtins.orByteString
  , 'Builtins.xorByteString
  , 'Builtins.complementByteString
  , 'Builtins.readBit
  , 'Builtins.writeBits
  , 'Builtins.replicateByte
  , 'Builtins.shiftByteString
  , 'Builtins.rotateByteString
  , 'Builtins.countSetBits
  , 'Builtins.findFirstSetBit
  , 'Builtins.expModInteger
  , ''Builtins.BuiltinValue
  , 'Builtins.insertCoin
  , 'Builtins.lookupCoin
  , 'Builtins.unionValue
  , 'Builtins.valueContains
  , 'Builtins.mkValue
  , 'Builtins.unsafeDataAsValue
  , 'Builtins.scaleValue
  ]

defineBuiltinTerm :: CompilingDefault uni fun m ann => Ann -> TH.Name -> PIRTerm uni fun -> m ()
defineBuiltinTerm ann name term = do
  ghcId <- lookupGhcId name
  var <- compileVarFresh ann ghcId
  binfo <- asks ccBuiltinsInfo
  -- See Note [Builtin terms and values]
  let strictness = if PIR.isPure binfo mempty term then PIR.Strict else PIR.NonStrict
      def = PIR.Def var (term, strictness)
  PIR.defineTerm (LexName $ GHC.getName ghcId) def mempty

-- | Add definitions for all the builtin types to the environment.
defineBuiltinType
  :: forall uni fun m ann. Compiling uni fun m ann => TH.Name -> PIRType uni -> m ()
defineBuiltinType name ty = do
  tc <- lookupGhcTyCon name
  var <- compileTcTyVarFresh tc
  PIR.defineType (LexName $ GHC.getName tc) (PIR.Def var ty) mempty
  -- these are all aliases for now
  PIR.recordAlias (LexName $ GHC.getName tc)

defineBoolType :: forall uni fun m ann. CompilingDefault uni fun m ann => m ()
defineBoolType = do
  datatypeStyle <- asks $ coDatatypeStyle . ccOpts

  defineBuiltinType ''Bool . ($> annMayInline) $ PLC.toTypeAst $ Proxy @Bool

  builtinBoolName <- LexName . GHC.getName <$> lookupGhcTyCon ''Bool
  boolTyCon <- lookupGhcTyCon ''Bool

  let
    -- We can assume there will be no type arguments for `Bool`. (That is unless GHC
    -- changes definintion of `Bool`, of course). Similarly, we can expect we always
    -- get correct number of branches, two.
    caseMatcher :: PIR.ManualMatcher uni fun Ann
    caseMatcher _tyArgs scrut resTy branches =
      case datatypeStyle of
        style
          | style == PIR.ScottEncoding || style == PIR.SumsOfProducts ->
              -- For IfThenElse, true branch comes first hence we reverse brenches
              PIR.mkIterApp
                ( PIR.tyInst
                    annMayInline
                    (PIR.builtin annMayInline PLC.IfThenElse)
                    resTy
                )
                ((annMayInline,) <$> (scrut : reverse branches))
        _BuiltinCasing ->
          PIR.kase annMayInline resTy scrut branches

  PIR.defineManualDatatype
    (LexName $ GHC.getName boolTyCon)
    ( PIR.ManualDatatype
        [PIR.mkConstant annAlwaysInline False, PIR.mkConstant annAlwaysInline True]
        caseMatcher
        []
    )
    (Set.fromList [builtinBoolName])

-- | Add definitions for all the builtin terms to the environment.
defineBuiltinTerms :: CompilingDefault uni fun m ann => m ()
defineBuiltinTerms = do
  datatypeStyle <- asks $ coDatatypeStyle . ccOpts
  -- Error
  -- See Note [Delaying error]
  func <- delayedErrorFunc
  -- We always want to inline `error :: forall a . () -> a`, hence `annAlwaysInline`.
  defineBuiltinTerm annAlwaysInline 'Builtins.error func

  -- Unit constant
  defineBuiltinTerm annMayInline 'Builtins.unitval $ PIR.mkConstant annMayInline ()

  -- ByteString constant
  defineBuiltinTerm annMayInline 'Builtins.emptyByteString $ PIR.mkConstant annMayInline BS.empty

  -- Text constant
  defineBuiltinTerm annMayInline 'Builtins.emptyString $ PIR.mkConstant annMayInline ("" :: Text)

  -- The next two constants are 48 bytes long, so in fact we may not want to inline them.
  defineBuiltinTerm annMayInline 'Builtins.bls12_381_G1_compressed_generator $
    PIR.mkConstant annMayInline BLS12_381.G1.compressed_generator
  defineBuiltinTerm annMayInline 'Builtins.bls12_381_G1_compressed_zero $
    PIR.mkConstant annMayInline BLS12_381.G1.compressed_zero

  -- The next two constants are 96 bytes long, so in fact we may not want to inline them.
  defineBuiltinTerm annMayInline 'Builtins.bls12_381_G2_compressed_generator $
    PIR.mkConstant annMayInline BLS12_381.G2.compressed_generator
  defineBuiltinTerm annMayInline 'Builtins.bls12_381_G2_compressed_zero $
    PIR.mkConstant annMayInline BLS12_381.G2.compressed_zero

  defineBuiltinTerm annMayInline 'Builtins.casePair $ case datatypeStyle of
    style | style == PIR.ScottEncoding || style == PIR.SumsOfProducts ->
      -- > /\a b r ->
      -- >   \(p : pair a b) (f : a -> b -> r) ->
      -- >     f (fstPair {a} {b} p) (sndPair {a} {b} p)
      fmap (const annMayInline) . runQuote $ do
        a <- freshTyName "a"
        b <- freshTyName "b"
        r <- freshTyName "r"
        p <- freshName "p"
        f <- freshName "f"
        let
          pairTy =
            PLC.TyApp
              ()
              ( PLC.TyApp
                  ()
                  (PLC.mkTyBuiltin @_ @(,) ())
                  (PLC.TyVar () a)
              )
              (PLC.TyVar () b)
          contTy =
            PLC.TyFun () (PLC.TyVar () a) $
              PLC.TyFun () (PLC.TyVar () b) (PLC.TyVar () r)

          instFstOrSnd x =
            PIR.tyInst () (PIR.tyInst () (PIR.builtin () x) (PLC.TyVar () a)) (PLC.TyVar () b)

        pure $
          PIR.tyAbs () a (PLC.Type ()) $
            PIR.tyAbs () b (PLC.Type ()) $
              PIR.tyAbs () r (PLC.Type ()) $
                PIR.lamAbs () p pairTy $
                  PIR.lamAbs () f contTy $
                    PIR.apply
                      ()
                      ( PIR.apply
                          ()
                          (PIR.var () f)
                          (PIR.apply () (instFstOrSnd PLC.FstPair) (PIR.var () p))
                      )
                      (PIR.apply () (instFstOrSnd PLC.SndPair) (PIR.var () p))
    _BuiltinCasing ->
      -- > /\a b r ->
      -- >   \(p : pair a b) (f : a -> b -> r) ->
      -- >     (case r p f)
      fmap (const annMayInline) . runQuote $ do
        a <- freshTyName "a"
        b <- freshTyName "b"
        r <- freshTyName "r"
        p <- freshName "p"
        f <- freshName "f"
        let
          pairTy =
            PLC.TyApp
              ()
              ( PLC.TyApp
                  ()
                  (PLC.mkTyBuiltin @_ @(,) ())
                  (PLC.TyVar () a)
              )
              (PLC.TyVar () b)
          contTy =
            PLC.TyFun () (PLC.TyVar () a) $
              PLC.TyFun () (PLC.TyVar () b) (PLC.TyVar () r)

        pure $
          PIR.tyAbs () a (PLC.Type ()) $
            PIR.tyAbs () b (PLC.Type ()) $
              PIR.tyAbs () r (PLC.Type ()) $
                PIR.lamAbs () p pairTy $
                  PIR.lamAbs () f contTy $
                    PIR.kase () (PLC.TyVar () r) (PIR.Var () p) [PIR.Var () f]

  defineBuiltinTerm annMayInline 'Builtins.caseList' $ case datatypeStyle of
    style | style == PIR.ScottEncoding || style == PIR.SumsOfProducts ->
      -- > /\a r ->
      -- >   \(z : r) (f : a -> list a -> r) (xs : list a) ->
      -- >     chooseList
      -- >       {a}
      -- >       {all dead. r}
      -- >       xs
      -- >       (/\dead -> z)
      -- >       (/\dead -> f (headList {a} xs) (tailList {a} xs))
      -- >       {r}
      fmap (const annMayInline) . runQuote $ do
        a <- freshTyName "a"
        r <- freshTyName "r"
        dead <- freshTyName "dead"
        xs <- freshName "xs"
        z <- freshName "z"
        f <- freshName "f"
        let listA = PLC.TyApp () (PLC.mkTyBuiltin @_ @[] ()) $ PLC.TyVar () a
            funAtXs headOrTail =
              PIR.apply
                ()
                (PIR.tyInst () (PIR.builtin () headOrTail) $ PLC.TyVar () a)
                (PIR.var () xs)
        return
          . PIR.tyAbs () a (PLC.Type ())
          . PIR.tyAbs () r (PLC.Type ())
          . PIR.lamAbs () z (PLC.TyVar () r)
          . PIR.lamAbs
            ()
            f
            (PLC.TyFun () (PLC.TyVar () a) . PLC.TyFun () listA $ PLC.TyVar () r)
          . PIR.lamAbs () xs listA
          . PIR.tyInst
            ()
            ( PIR.mkIterAppNoAnn
                ( PIR.mkIterInstNoAnn
                    (PIR.builtin () PLC.ChooseList)
                    [ PLC.TyVar () a
                    , PLC.TyForall () dead (PLC.Type ()) $ PLC.TyVar () r
                    ]
                )
                [ PIR.var () xs
                , PIR.tyAbs () dead (PLC.Type ()) $ PIR.var () z
                , PIR.tyAbs () dead (PLC.Type ()) $
                    PIR.mkIterAppNoAnn
                      (PIR.var () f)
                      [funAtXs PLC.HeadList, funAtXs PLC.TailList]
                ]
            )
          $ PLC.TyVar () r
    _BuiltinCasing ->
      -- > /\a r ->
      -- >   \(z : r) (f : a -> list a -> r) (xs : list a) ->
      -- >     (case r xs f z)
      fmap (const annMayInline) . runQuote $ do
        a <- freshTyName "a"
        r <- freshTyName "r"
        xs <- freshName "xs"
        z <- freshName "z"
        f <- freshName "f"
        let listA = PLC.TyApp () (PLC.mkTyBuiltin @_ @[] ()) $ PLC.TyVar () a
        return $
          PIR.tyAbs () a (PLC.Type ()) $
            PIR.tyAbs () r (PLC.Type ()) $
              PIR.lamAbs () z (PLC.TyVar () r) $
                PIR.lamAbs () f (PLC.TyFun () (PLC.TyVar () a) . PLC.TyFun () listA $ PLC.TyVar () r) $
                  PIR.lamAbs () xs listA $
                    PIR.kase
                      ()
                      (PLC.TyVar () r)
                      (PIR.var () xs)
                      [PIR.var () f, PIR.var () z]

  -- See Note [Builtin terms and values]
  for_ enumerate $ \fun ->
    let defineBuiltinInl impl = defineBuiltinTerm annMayInline impl $ mkBuiltin fun
     in case fun of
          PLC.IfThenElse -> case datatypeStyle of
            PIR.ScottEncoding -> defineBuiltinInl 'Builtins.ifThenElse
            PIR.SumsOfProducts -> defineBuiltinInl 'Builtins.ifThenElse
            PIR.BuiltinCasing -> defineBuiltinTerm annMayInline 'Builtins.ifThenElse $
              fmap (const annMayInline) . runQuote $ do
                a <- freshTyName "a"
                b <- freshName "b"
                x <- freshName "x"
                y <- freshName "y"
                return
                  . PIR.tyAbs () a (PLC.Type ())
                  . PIR.lamAbs () b (PLC.mkTyBuiltin @_ @Bool ())
                  . PIR.lamAbs () x (PLC.TyVar () a)
                  . PIR.lamAbs () y (PLC.TyVar () a)
                  $ PIR.kase
                    ()
                    (PLC.TyVar () a)
                    (PIR.Var () b)
                    [PIR.Var () y, PIR.Var () x]
          PLC.ChooseUnit -> case datatypeStyle of
            PIR.ScottEncoding -> defineBuiltinInl 'Builtins.chooseUnit
            PIR.SumsOfProducts -> defineBuiltinInl 'Builtins.chooseUnit
            PIR.BuiltinCasing -> defineBuiltinTerm annMayInline 'Builtins.chooseUnit $
              fmap (const annMayInline) . runQuote $ do
                r <- freshTyName "r"
                unit <- freshName "unit"
                x <- freshName "x"
                return $
                  PIR.tyAbs () r (PLC.Type ()) $
                    PIR.lamAbs () unit (PLC.mkTyBuiltin @_ @() ()) $
                      PIR.lamAbs () x (PLC.TyVar () r) $
                        PIR.kase
                          ()
                          (PLC.TyVar () r)
                          (PIR.Var () unit)
                          [PIR.var () x]
          -- Bytestrings
          PLC.AppendByteString -> defineBuiltinInl 'Builtins.appendByteString
          PLC.ConsByteString -> defineBuiltinInl 'Builtins.consByteString
          PLC.SliceByteString -> defineBuiltinInl 'Builtins.sliceByteString
          PLC.LengthOfByteString -> defineBuiltinInl 'Builtins.lengthOfByteString
          PLC.IndexByteString -> defineBuiltinInl 'Builtins.indexByteString
          PLC.Sha2_256 -> defineBuiltinInl 'Builtins.sha2_256
          PLC.Sha3_256 -> defineBuiltinInl 'Builtins.sha3_256
          PLC.Blake2b_224 -> defineBuiltinInl 'Builtins.blake2b_224
          PLC.Blake2b_256 -> defineBuiltinInl 'Builtins.blake2b_256
          PLC.Keccak_256 -> defineBuiltinInl 'Builtins.keccak_256
          PLC.Ripemd_160 -> defineBuiltinInl 'Builtins.ripemd_160
          PLC.EqualsByteString -> defineBuiltinInl 'Builtins.equalsByteString
          PLC.LessThanByteString -> defineBuiltinInl 'Builtins.lessThanByteString
          PLC.LessThanEqualsByteString -> defineBuiltinInl 'Builtins.lessThanEqualsByteString
          PLC.DecodeUtf8 -> defineBuiltinInl 'Builtins.decodeUtf8
          -- Strings and chars
          PLC.AppendString -> defineBuiltinInl 'Builtins.appendString
          PLC.EqualsString -> defineBuiltinInl 'Builtins.equalsString
          PLC.EncodeUtf8 -> defineBuiltinInl 'Builtins.encodeUtf8
          -- Crypto
          PLC.VerifyEd25519Signature -> defineBuiltinInl 'Builtins.verifyEd25519Signature
          PLC.VerifyEcdsaSecp256k1Signature -> defineBuiltinInl 'Builtins.verifyEcdsaSecp256k1Signature
          PLC.VerifySchnorrSecp256k1Signature -> defineBuiltinInl 'Builtins.verifySchnorrSecp256k1Signature
          -- Integers
          PLC.AddInteger -> defineBuiltinInl 'Builtins.addInteger
          PLC.SubtractInteger -> defineBuiltinInl 'Builtins.subtractInteger
          PLC.MultiplyInteger -> defineBuiltinInl 'Builtins.multiplyInteger
          PLC.DivideInteger -> defineBuiltinInl 'Builtins.divideInteger
          PLC.ModInteger -> defineBuiltinInl 'Builtins.modInteger
          PLC.QuotientInteger -> defineBuiltinInl 'Builtins.quotientInteger
          PLC.RemainderInteger -> defineBuiltinInl 'Builtins.remainderInteger
          PLC.LessThanInteger -> defineBuiltinInl 'Builtins.lessThanInteger
          PLC.LessThanEqualsInteger -> defineBuiltinInl 'Builtins.lessThanEqualsInteger
          PLC.EqualsInteger -> defineBuiltinInl 'Builtins.equalsInteger
          -- Tracing
          PLC.Trace -> defineBuiltinInl 'Builtins.trace
          -- Pairs
          PLC.FstPair -> case datatypeStyle of
            PIR.ScottEncoding -> defineBuiltinInl 'Builtins.fst
            PIR.SumsOfProducts -> defineBuiltinInl 'Builtins.fst
            PIR.BuiltinCasing -> defineBuiltinTerm annMayInline 'Builtins.fst $
              fmap (const annMayInline) . runQuote $ do
                a <- freshTyName "a"
                b <- freshTyName "b"
                x <- freshName "x"
                l <- freshName "l"
                r <- freshName "r"
                let
                  pairTy =
                    PLC.TyApp
                      ()
                      ( PLC.TyApp
                          ()
                          (PLC.mkTyBuiltin @_ @(,) ())
                          (PLC.TyVar () a)
                      )
                      (PLC.TyVar () b)
                return $
                  PIR.tyAbs () a (PLC.Type ()) $
                    PIR.tyAbs () b (PLC.Type ()) $
                      PIR.lamAbs () x pairTy $
                        PIR.kase
                          ()
                          (PLC.TyVar () a)
                          (PIR.Var () x)
                          [ PIR.lamAbs () l (PLC.TyVar () a) $
                              PIR.lamAbs () r (PLC.TyVar () b) $
                                PIR.var () l
                          ]
          PLC.SndPair -> case datatypeStyle of
            PIR.ScottEncoding -> defineBuiltinInl 'Builtins.snd
            PIR.SumsOfProducts -> defineBuiltinInl 'Builtins.snd
            PIR.BuiltinCasing -> defineBuiltinTerm annMayInline 'Builtins.snd $
              fmap (const annMayInline) . runQuote $ do
                a <- freshTyName "a"
                b <- freshTyName "b"
                x <- freshName "x"
                l <- freshName "l"
                r <- freshName "r"
                let
                  pairTy =
                    PLC.TyApp
                      ()
                      ( PLC.TyApp
                          ()
                          (PLC.mkTyBuiltin @_ @(,) ())
                          (PLC.TyVar () a)
                      )
                      (PLC.TyVar () b)
                return $
                  PIR.tyAbs () a (PLC.Type ()) $
                    PIR.tyAbs () b (PLC.Type ()) $
                      PIR.lamAbs () x pairTy $
                        PIR.kase
                          ()
                          (PLC.TyVar () b)
                          (PIR.Var () x)
                          [ PIR.lamAbs () l (PLC.TyVar () a) $
                              PIR.lamAbs () r (PLC.TyVar () b) $
                                PIR.var () r
                          ]
          PLC.MkPairData -> defineBuiltinInl 'Builtins.mkPairData
          -- List
          PLC.NullList -> defineBuiltinInl 'Builtins.null
          PLC.HeadList -> defineBuiltinInl 'Builtins.head
          PLC.TailList -> defineBuiltinInl 'Builtins.tail
          PLC.ChooseList -> defineBuiltinInl 'Builtins.chooseList
          PLC.MkNilData -> defineBuiltinInl 'Builtins.mkNilData
          PLC.MkNilPairData -> defineBuiltinInl 'Builtins.mkNilPairData
          PLC.MkCons -> defineBuiltinInl 'Builtins.mkCons
          PLC.DropList -> defineBuiltinInl 'Builtins.drop
          -- Arrays
          PLC.LengthOfArray -> defineBuiltinInl 'Builtins.lengthOfArray
          PLC.ListToArray -> defineBuiltinInl 'Builtins.listToArray
          PLC.IndexArray -> defineBuiltinInl 'Builtins.indexArray
          -- Data
          PLC.ChooseData -> defineBuiltinInl 'Builtins.chooseData
          PLC.EqualsData -> defineBuiltinInl 'Builtins.equalsData
          PLC.ConstrData -> defineBuiltinInl 'Builtins.mkConstr
          PLC.MapData -> defineBuiltinInl 'Builtins.mkMap
          PLC.ListData -> defineBuiltinInl 'Builtins.mkList
          PLC.IData -> defineBuiltinInl 'Builtins.mkI
          PLC.BData -> defineBuiltinInl 'Builtins.mkB
          PLC.UnConstrData -> defineBuiltinInl 'Builtins.unsafeDataAsConstr
          PLC.UnMapData -> defineBuiltinInl 'Builtins.unsafeDataAsMap
          PLC.UnListData -> defineBuiltinInl 'Builtins.unsafeDataAsList
          PLC.ArrayData -> defineBuiltinInl 'Builtins.mkArray
          PLC.UnArrayData -> defineBuiltinInl 'Builtins.unsafeDataAsArray
          PLC.UnBData -> defineBuiltinInl 'Builtins.unsafeDataAsB
          PLC.UnIData -> defineBuiltinInl 'Builtins.unsafeDataAsI
          PLC.SerialiseData -> defineBuiltinInl 'Builtins.serialiseData
          -- BLS
          PLC.Bls12_381_G1_equal -> defineBuiltinInl 'Builtins.bls12_381_G1_equals
          PLC.Bls12_381_G1_add -> defineBuiltinInl 'Builtins.bls12_381_G1_add
          PLC.Bls12_381_G1_neg -> defineBuiltinInl 'Builtins.bls12_381_G1_neg
          PLC.Bls12_381_G1_scalarMul -> defineBuiltinInl 'Builtins.bls12_381_G1_scalarMul
          PLC.Bls12_381_G1_multiScalarMul -> defineBuiltinInl 'Builtins.bls12_381_G1_multiScalarMul
          PLC.Bls12_381_G1_compress -> defineBuiltinInl 'Builtins.bls12_381_G1_compress
          PLC.Bls12_381_G1_uncompress -> defineBuiltinInl 'Builtins.bls12_381_G1_uncompress
          PLC.Bls12_381_G1_hashToGroup -> defineBuiltinInl 'Builtins.bls12_381_G1_hashToGroup
          PLC.Bls12_381_G2_equal -> defineBuiltinInl 'Builtins.bls12_381_G2_equals
          PLC.Bls12_381_G2_add -> defineBuiltinInl 'Builtins.bls12_381_G2_add
          PLC.Bls12_381_G2_scalarMul -> defineBuiltinInl 'Builtins.bls12_381_G2_scalarMul
          PLC.Bls12_381_G2_multiScalarMul -> defineBuiltinInl 'Builtins.bls12_381_G2_multiScalarMul
          PLC.Bls12_381_G2_neg -> defineBuiltinInl 'Builtins.bls12_381_G2_neg
          PLC.Bls12_381_G2_compress -> defineBuiltinInl 'Builtins.bls12_381_G2_compress
          PLC.Bls12_381_G2_uncompress -> defineBuiltinInl 'Builtins.bls12_381_G2_uncompress
          PLC.Bls12_381_G2_hashToGroup -> defineBuiltinInl 'Builtins.bls12_381_G2_hashToGroup
          PLC.Bls12_381_millerLoop -> defineBuiltinInl 'Builtins.bls12_381_millerLoop
          PLC.Bls12_381_mulMlResult -> defineBuiltinInl 'Builtins.bls12_381_mulMlResult
          PLC.Bls12_381_finalVerify -> defineBuiltinInl 'Builtins.bls12_381_finalVerify
          -- Bitwise operations
          PLC.IntegerToByteString -> defineBuiltinInl 'Builtins.integerToByteString
          PLC.ByteStringToInteger -> defineBuiltinInl 'Builtins.byteStringToInteger
          -- Logical operations
          PLC.AndByteString -> defineBuiltinInl 'Builtins.andByteString
          PLC.OrByteString -> defineBuiltinInl 'Builtins.orByteString
          PLC.XorByteString -> defineBuiltinInl 'Builtins.xorByteString
          PLC.ComplementByteString -> defineBuiltinInl 'Builtins.complementByteString
          PLC.ReadBit -> defineBuiltinInl 'Builtins.readBit
          PLC.WriteBits -> defineBuiltinInl 'Builtins.writeBits
          PLC.ReplicateByte -> defineBuiltinInl 'Builtins.replicateByte
          -- Other bitwise ops
          PLC.ShiftByteString -> defineBuiltinInl 'Builtins.shiftByteString
          PLC.RotateByteString -> defineBuiltinInl 'Builtins.rotateByteString
          PLC.CountSetBits -> defineBuiltinInl 'Builtins.countSetBits
          PLC.FindFirstSetBit -> defineBuiltinInl 'Builtins.findFirstSetBit
          PLC.ExpModInteger -> defineBuiltinInl 'Builtins.expModInteger
          -- Value
          PLC.InsertCoin -> defineBuiltinInl 'Builtins.insertCoin
          PLC.LookupCoin -> defineBuiltinInl 'Builtins.lookupCoin
          PLC.UnionValue -> defineBuiltinInl 'Builtins.unionValue
          PLC.ValueContains -> defineBuiltinInl 'Builtins.valueContains
          PLC.ValueData -> defineBuiltinInl 'Builtins.mkValue
          PLC.UnValueData -> defineBuiltinInl 'Builtins.unsafeDataAsValue
          PLC.ScaleValue -> defineBuiltinInl 'Builtins.scaleValue

defineBuiltinTypes :: CompilingDefault uni fun m ann => m ()
defineBuiltinTypes = do
  defineBuiltinType ''Builtins.BuiltinByteString . ($> annMayInline) $
    PLC.toTypeAst $
      Proxy @BS.ByteString
  defineBuiltinType ''Integer . ($> annMayInline) $ PLC.toTypeAst $ Proxy @Integer
  defineBuiltinType ''Builtins.BuiltinUnit . ($> annMayInline) $ PLC.toTypeAst $ Proxy @()
  defineBuiltinType ''Builtins.BuiltinString . ($> annMayInline) $ PLC.toTypeAst $ Proxy @Text
  defineBuiltinType ''Builtins.BuiltinData . ($> annMayInline) $ PLC.toTypeAst $ Proxy @PLC.Data
  defineBuiltinType ''Builtins.BuiltinPair . ($> annMayInline) $
    PLC.TyBuiltin () (PLC.SomeTypeIn PLC.DefaultUniProtoPair)
  defineBuiltinType ''Builtins.BuiltinList . ($> annMayInline) $
    PLC.TyBuiltin () (PLC.SomeTypeIn PLC.DefaultUniProtoList)
  defineBuiltinType ''Builtins.BuiltinArray . ($> annMayInline) $
    PLC.TyBuiltin () (PLC.SomeTypeIn PLC.DefaultUniProtoArray)
  defineBuiltinType ''Builtins.BuiltinBLS12_381_G1_Element . ($> annMayInline) $
    PLC.toTypeAst $
      Proxy @BLS12_381.G1.Element
  defineBuiltinType ''Builtins.BuiltinBLS12_381_G2_Element . ($> annMayInline) $
    PLC.toTypeAst $
      Proxy @BLS12_381.G2.Element
  defineBuiltinType ''Builtins.BuiltinBLS12_381_MlResult . ($> annMayInline) $
    PLC.toTypeAst $
      Proxy @BLS12_381.Pairing.MlResult
  defineBuiltinType ''Builtins.BuiltinValue . ($> annMayInline) $ PLC.toTypeAst $ Proxy @Value

-- | Lookup a builtin term by its TH name. These are assumed to be present, so fails if it cannot find it.
lookupBuiltinTerm :: Compiling uni fun m ann => TH.Name -> m (PIRTerm uni fun)
lookupBuiltinTerm name = do
  ghcName <- lookupGhcName name
  maybeTerm <- PIR.lookupTerm (LexName ghcName)
  case maybeTerm of
    Just t -> pure t
    Nothing -> throwSd CompilationError $ "Missing builtin definition:" GHC.<+> (GHC.text $ show name)

-- | Lookup a builtin type by its TH name. These are assumed to be present, so fails if it is cannot find it.
lookupBuiltinType :: Compiling uni fun m ann => TH.Name -> m (PIRType uni)
lookupBuiltinType name = do
  ghcName <- lookupGhcName name
  maybeType <- PIR.lookupType annMayInline (LexName ghcName)
  case maybeType of
    Just t -> pure t
    Nothing -> throwSd CompilationError $ "Missing builtin definition:" GHC.<+> (GHC.text $ show name)

-- | The function 'error :: forall a . a'.
errorFunc :: Compiling uni fun m ann => m (PIRTerm uni fun)
errorFunc = do
  n <- safeFreshTyName "e"
  pure $
    PIR.TyAbs annMayInline n (PIR.Type annMayInline) (PIR.Error annMayInline (PIR.TyVar annMayInline n))

-- | The delayed error function 'error :: forall a . () -> a'.
delayedErrorFunc :: CompilingDefault uni fun m ann => m (PIRTerm uni fun)
delayedErrorFunc = do
  n <- safeFreshTyName "a"
  t <- liftQuote (freshName "thunk")
  let ty = PLC.toTypeAst $ Proxy @()
  pure $
    PIR.TyAbs annMayInline n (PIR.Type annMayInline) $
      PIR.LamAbs annMayInline t (ty $> annMayInline) $
        PIR.Error annMayInline (PIR.TyVar annMayInline n)
