{-# LANGUAGE BangPatterns       #-}
{-# LANGUAGE DeriveAnyClass     #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE LambdaCase         #-}
{-# LANGUAGE MultiWayIf         #-}
{-# LANGUAGE OverloadedStrings  #-}
{-# LANGUAGE ViewPatterns       #-}

module PlutusTx.Data (Data (..)) where

import qualified Codec.CBOR.Term           as CBOR
import           Codec.Serialise           (Serialise (..))
import           Control.DeepSeq           (NFData)
import           Control.Monad.Except
import           Data.Bifunctor            (bimap)
import qualified Data.ByteString           as BS
import qualified Data.ByteString.Lazy      as BSL
import           Data.Text.Prettyprint.Doc
import           GHC.Generics
import           Prelude

-- | A generic "data" type.
--
-- The main constructor 'Constr' represents a datatype value in sum-of-products
-- form: @Constr i args@ represents a use of the @i@th constructor along with its arguments.
--
-- The other constructors are various primitives.
data Data =
      Constr Integer [Data]
    | Map [(Data, Data)]
    | List [Data]
    | I Integer
    | B BS.ByteString
    deriving stock (Show, Eq, Ord, Generic)
    deriving anyclass (NFData)

instance Pretty Data where
    pretty = \case
        Constr _ ds -> angles (sep (punctuate comma (fmap pretty ds)))
        Map entries -> braces (sep (punctuate comma (fmap (\(k, v) -> pretty k <> ":" <+> pretty v) entries)))
        List ds     -> brackets (sep (punctuate comma (fmap pretty ds)))
        I i         -> pretty i
        B b         -> viaShow b

{- Note [Encoding via Term]
We want to write a custom encoder/decoder for Data (i.e. not use the Generic version), but actually
doing this is a pain. So instead we go via the CBOR 'Term' representation, which lets us process a
more structured representation, which is a lot easier.
-}

instance Serialise Data where
    -- See Note [Encoding via Term]
    encode = CBOR.encodeTerm . toTerm
    decode = do
        t <- CBOR.decodeTerm
        case fromTerm t of
            Right d -> pure d
            Left e  -> fail e

{- Note [CBOR alternative tags]
We've proposed to add additional tags to the CBOR standard to cover (essentially) sum types.
This is exactly what we need to encode the 'Constr' constructor of 'Data' in an unambiguous way.

The tags aren't *quite* accepted yet, but they're clearly going to accept so we might as well
start using them.

The scheme is:
- Alternatives 0-6 -> tags 121-127
- Alternatives 7-127 -> tags 1280-1400
- Any alternatives, including those that don't fit in the above -> tag 102 followed by an integer for the actual alternative.
-}

-- | Turn Data into a CBOR Term.
toTerm :: Data -> CBOR.Term
toTerm = \case
    -- See Note [CBOR alternative tags]
    Constr i ds | 0 <= i && i < 7   -> CBOR.TTagged (fromIntegral (121 + i)) (CBOR.TList $ fmap toTerm ds)
    Constr i ds | 7 <= i && i < 128 -> CBOR.TTagged (fromIntegral (1280 + (i - 7))) (CBOR.TList $ fmap toTerm ds)
    Constr i ds | otherwise         -> CBOR.TTagged 102 (CBOR.TList $ CBOR.TInteger i : fmap toTerm ds)
    Map es                          -> CBOR.TMap (fmap (bimap toTerm toTerm) es)
    List ds                         -> CBOR.TList $ fmap toTerm ds
    I i                             -> CBOR.TInteger i
    B b                             -> CBOR.TBytes b

{- Note [Definite and indefinite forms of CBOR]
CBOR is annoying and you can have both definite (with a fixed length) and indefinite lists, maps, etc.

So we have to be careful to handle both cases when decoding. When encoding we simply don't make
the indefinite kinds.
-}

-- | Turn a CBOR Term into Data if possible.
fromTerm :: CBOR.Term -> Either String Data
fromTerm = \case
    -- See Note [CBOR alternative tags]
    CBOR.TTagged t (CBOR.TList ds)
        | 121  <= t && t < 128                -> Constr (fromIntegral t - 121) <$> traverse fromTerm ds
    CBOR.TTagged t (CBOR.TList ds)
        | 1280 <= t && t < 1401               -> Constr ((fromIntegral t - 1280) + 7) <$> traverse fromTerm ds
    CBOR.TTagged t (CBOR.TList (i:ds))
        | t == 102, Just actualTag <- asInt i -> Constr actualTag <$> traverse fromTerm ds
    CBOR.TTagged _ _                          -> throwError "Couldn't interpret tag as constructor tag"
    -- See Note [Definite and indefinite forms of CBOR]
    CBOR.TMap es                              -> Map <$> traverse (\(t1, t2) -> (,) <$> fromTerm t1 <*> fromTerm t2) es
    CBOR.TMapI es                             -> Map <$> traverse (\(t1, t2) -> (,) <$> fromTerm t1 <*> fromTerm t2) es
    CBOR.TList l                              -> List <$> traverse fromTerm l
    CBOR.TListI l                             -> List <$> traverse fromTerm l
    CBOR.TInteger i                           -> pure $ I i
    CBOR.TInt i                               -> pure $ I $ fromIntegral i
    CBOR.TBytes b                             -> pure $ B b
    CBOR.TBytesI b                            -> pure $ B $ BSL.toStrict b
    _                                         -> throwError "Unsupported kind of CBOR"

-- See Note [Definite and indefinite forms of CBOR]
-- | View a CBOR Term as an Integer if possible.
asInt :: CBOR.Term -> Maybe Integer
asInt (CBOR.TInteger i) = Just i
asInt (CBOR.TInt i)     = Just $ fromIntegral i
asInt _                 = Nothing
