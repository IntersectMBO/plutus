{-# LANGUAGE AllowAmbiguousTypes  #-}
{-# LANGUAGE DataKinds            #-}
{-# LANGUAGE DefaultSignatures    #-}
{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE GADTs                #-}
{-# LANGUAGE OverloadedStrings    #-}
{-# LANGUAGE PolyKinds            #-}
{-# LANGUAGE RankNTypes           #-}
{-# LANGUAGE RecordWildCards      #-}
{-# LANGUAGE ScopedTypeVariables  #-}
{-# LANGUAGE TypeApplications     #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}

module IOTS
  ( export
  , IotsExportable
  , IotsType(iotsDefinition)
  , IotsBuilder(..)
  , HList(HNil, HCons)
  , Tagged(Tagged)
  ) where

import           Control.Monad.State          (State, evalState, foldM, gets, modify)
import           Data.Foldable                (fold, toList)
import           Data.Kind                    (Type)
import           Data.Map                     (Map)
import           Data.Proxy                   (Proxy (Proxy))
import           Data.Sequence                (Seq, (|>))
import           Data.Set                     (Set)
import qualified Data.Set                     as Set
import           Data.Tagged                  (Tagged (Tagged))
import           Data.Text                    (Text)
import qualified Data.Text                    as Text
import           Data.Tree                    (Forest, Tree (Node), rootLabel)
import           GHC.Generics                 (C1, Constructor, D1, Datatype, Generic, M1 (M1), Rec0, Rep, S1, Selector,
                                               U1, conIsRecord, conName, selName, (:*:) ((:*:)), (:+:))
import qualified GHC.Generics                 as Generics
import           GHC.TypeLits                 (KnownSymbol, symbolVal)
import           IOTS.Leijen                  (jsArray, jsObject, jsParams, render, stringDoc, symbol, upperFirst)
import           IOTS.Tree                    (depthfirstM)
import           Text.PrettyPrint.Leijen.Text (Doc, angles, braces, comma, dquotes, hsep, linebreak, parens, punctuate,
                                               semi, squotes, textStrict, vsep, (<+>))
import           Type.Reflection              (SomeTypeRep (SomeTypeRep), Typeable, someTypeRep)
import qualified Type.Reflection              as R

{-# ANN module ("HLint: ignore Avoid restricted function" :: Text)
        #-}

data IotsTypeRep a where
  Atom :: IotsType a => IotsTypeRep a
  Group
    :: IotsTypeRep a -> IotsTypeRep (HList bs) -> IotsTypeRep (HList (a ': bs))
  Fun
    :: IotsTypeRep a
    -> IotsTypeRep b
    -> IotsTypeRep (a -> b)
  NamedFun :: Typeable f => Text -> IotsTypeRep (a -> b) -> IotsTypeRep f

------------------------------------------------------------
-- | Accumulates the data we need to write out the final JavaScript string.
data IotsBuilder =
  IotsBuilder
    { iotsRep    :: SomeTypeRep
        -- ^ The type this record describes.
    , iotsRef    :: Doc
        -- ^ How we refer to this type. For IOTS builtins this is
        -- probably 't.something'. For our definitions it will the the
        -- type name (eg. 'User').
    , iotsOutput :: Bool
        -- ^ Should we write this type out in the final export?
    }
  deriving (Show)

repName :: SomeTypeRep -> Doc
repName = stringDoc . fold . go
  where
    go :: SomeTypeRep -> [String]
    go rep@(SomeTypeRep someRep)
      | rep == R.someTypeRep (Proxy @String) = ["String"]
      | otherwise = headName : foldMap go params
      where
        (tyCon, params) = R.splitApps someRep
        headName =
          case R.tyConName tyCon of
            "[]"  -> "List"
            other -> other

toRef :: Tree IotsBuilder -> Doc
toRef = iotsRef . rootLabel

------------------------------------------------------------
-- | Render out a type, function or 'HList' of functions as an IOTS-compatible definition file.
--
-- All the subtypes needed for compilation will also be exported, as long as they are all 'IotsExportable'.
--
-- Example usage:
--
-- @
--    iotsDefinition :: Text
--    iotsDefinition = export (Tagged @"maybeFunction" f)
--      where
--        f :: Maybe User -> String
--        f _ = "foo"
-- @
--
-- Assuming that 'User' implements 'IotsType', then `iotsDefinition`
-- will contain an IOTS script defining 'User' and a function named
-- 'maybeFunction'. Note that you do not need to export 'User'
-- explicitly.
export ::
     forall a. IotsExportable a
  => a
  -> Text
export _ =
  render . vsep . punctuate linebreak . toList $ definitions
  where
    definitions :: Seq Doc
    definitions =
      flip evalState mempty .
      foldM (depthfirstM appendUnseenDefinitions) mempty .
      flip evalState mempty . gatherDefinitions $
      iotsTypeRep @a
    appendUnseenDefinitions ::
         Seq Doc -> IotsBuilder -> State (Set SomeTypeRep) (Seq Doc)
    appendUnseenDefinitions acc IotsBuilder {..} = do
      seen <- gets (Set.member iotsRep)
      modify (Set.insert iotsRep)
      pure $
        if iotsOutput && not seen
          then acc |> iotsRef
          else acc

------------------------------------------------------------
type Visited = Set SomeTypeRep

gatherDefinitions :: forall a. IotsTypeRep a -> State Visited (Forest IotsBuilder)
gatherDefinitions Atom = iotsDefinition @a
gatherDefinitions (Group x xs) =
  mappend <$> gatherDefinitions x <*> gatherDefinitions xs
gatherDefinitions (Fun from to) =
  mappend <$> gatherDefinitions from <*> gatherDefinitions to
gatherDefinitions (NamedFun functionName fun) = do
    children <- gatherDefinitions fun
    let inputArguments = init children
        outputArgument = last children
        labelledParameter :: Text -> Tree IotsBuilder -> Doc
        labelledParameter argName def =
            textStrict argName <> ":" <+> toRef def
        functionBinding = textStrict (upperFirst functionName)
        toBinding argName = functionBinding <> textStrict argName
        argsBinding = toBinding "Args"
        returnBinding = toBinding "Return"
        typeSignature = "t.type" <> parens (jsObject (withParameterLabels labelledParameter inputArguments))

        iotsRep = someTypeRep (Proxy @a)
        iotsOutput = True
        iotsRef =
            vsep . punctuate linebreak $
            [ "const" <+> argsBinding <+> "=" <+> typeSignature <> semi
            , "const" <+> returnBinding <+> "=" <+> toRef outputArgument <> semi
            , "export" <+> "const" <+>
              functionBinding <+>
              "=" <+>
              "createEndpoint" <>
              angles
                  (hsep
                       (punctuate
                            comma
                            [ "typeof" <+> argsBinding
                            , "typeof" <+> returnBinding
                            , "t.NullC"
                            ])) <>
              jsParams [squotes functionBinding, argsBinding, returnBinding] <>
              semi
            ]
    pure [Node (IotsBuilder {..}) children]

withParameterLabels :: (Text -> Tree IotsBuilder -> Doc) -> Forest IotsBuilder -> [Doc]
withParameterLabels f = zipWith f (Text.singleton <$> ['a' .. 'z'])

------------------------------------------------------------
-- | A type-level list.
-- This helps us create a list of different type signatures to export.
data HList (ts :: [Type]) where
  HNil :: HList '[]
  HCons :: t -> HList ts -> HList (t ': ts)
  deriving (Typeable)

------------------------------------------------------------
-- | Something that we can export to an IOTS definition. In general this is:
--
--     * Any type that implements 'IotsType'.
--     * Any function that only references 'IotsType's.
--     * An 'HList' containing a mixture of those.
class IotsExportable a where
  iotsTypeRep :: IotsTypeRep a

instance {-# OVERLAPPABLE #-} IotsType a => IotsExportable a where
  iotsTypeRep = Atom

instance IotsExportable (HList '[]) where
  iotsTypeRep = Atom

instance (IotsExportable t, IotsExportable (HList ts)) =>
         IotsExportable (HList (t ': ts)) where
  iotsTypeRep = Group iotsTypeRep iotsTypeRep

instance (IotsExportable a, IotsExportable b) =>
         IotsExportable ((->) a b) where
  iotsTypeRep = Fun iotsTypeRep iotsTypeRep

instance (KnownSymbol s, IotsExportable (a -> b), Typeable (a -> b)) =>
         IotsExportable (Tagged s (a -> b)) where
  iotsTypeRep =
    NamedFun (Text.pack (symbolVal (Proxy @s))) (iotsTypeRep @(a -> b))

------------------------------------------------------------
-- | Any type we can teach IOTS about. For most cases it will be sufficient to add:
--
--   > deriving (Generic, IotsType)
--
-- ...to your definition.
class IotsType a where
  iotsDefinition :: State Visited (Forest IotsBuilder)
  default iotsDefinition :: (Typeable a, Generic a, GenericIotsType (Rep a)) =>
    State Visited (Forest IotsBuilder)
  iotsDefinition =
    genericTypeReps (someTypeRep (Proxy @a)) $ Generics.from (undefined :: a)

instance IotsType Text where
  iotsDefinition = pure [Node (IotsBuilder {..}) []]
    where
      iotsRep = someTypeRep (Proxy @Text)
      iotsOutput = False
      iotsRef = "t.string"

instance IotsType Char where
  iotsDefinition = pure [Node (IotsBuilder {..}) []]
    where
      iotsRep = someTypeRep (Proxy @Char)
      iotsOutput = False
      iotsRef = "t.string"

instance IotsType Integer where
  iotsDefinition = pure [Node (IotsBuilder {..}) []]
    where
      iotsRep = someTypeRep (Proxy @Integer)
      iotsOutput = False
      iotsRef = "t.number"

instance IotsType Int where
  iotsDefinition = pure [Node (IotsBuilder {..}) []]
    where
      iotsRep = someTypeRep (Proxy @Int)
      iotsOutput = False
      iotsRef = "t.number"

instance IotsType Bool where
  iotsDefinition = pure [Node (IotsBuilder {..}) []]
    where
      iotsRep = someTypeRep (Proxy @Bool)
      iotsOutput = False
      iotsRef = "t.boolean"

instance IotsType a => IotsType (Proxy a) where
  iotsDefinition = iotsDefinition @a

instance (IotsType a, IotsType b, Typeable a, Typeable b) =>
         IotsType (a, b) where
  iotsDefinition = do
    leftReps <- iotsDefinition @a
    rightReps <- iotsDefinition @b
    let children = leftReps <> rightReps
        iotsRep = someTypeRep (Proxy @(a, b))
        iotsOutput = False
        iotsRef = "t.tuple" <> parens (jsArray (toRef <$> children))
    pure [Node (IotsBuilder {..}) children]

instance (IotsType k, IotsType v, Typeable k, Typeable v) =>
         IotsType (Map k v) where
  iotsDefinition = do
    keyReps <- iotsDefinition @k
    valueReps <- iotsDefinition @v
    let children = keyReps <> valueReps
        iotsRep = someTypeRep (Proxy @(Map k v))
        iotsOutput = False
        iotsRef = "t.record" <> jsParams (toRef <$> children)
    pure [Node (IotsBuilder {..}) children]

instance IotsType () where
  iotsDefinition = do
    let iotsRep = someTypeRep (Proxy @())
        iotsOutput = False
        iotsRef = "t.null"
    pure [Node (IotsBuilder {..}) []]

instance (IotsType a, Typeable a) => IotsType (Maybe a) where
  iotsDefinition = do
    aChildren <- iotsDefinition @a
    nothingChildren <- iotsDefinition @()
    let children = aChildren <> nothingChildren
        iotsRep = someTypeRep (Proxy @(Maybe a))
        iotsOutput = False
        iotsRef = "t.union" <> parens (jsArray (toRef <$> children))
    pure [Node (IotsBuilder {..}) children]

instance (IotsType a, Typeable a, IotsType b, Typeable b) => IotsType (Either a b) where
  iotsDefinition = do
    aChildren <- iotsDefinition @a
    bChildren <- iotsDefinition @b
    let children = aChildren <> bChildren
        iotsRep = someTypeRep (Proxy @(Either a b))
        iotsOutput = False
        iotsRef = "t.union" <> parens (jsArray (toRef <$> children))
    pure [Node (IotsBuilder {..}) children]

------------------------------------------------------------
instance {-# OVERLAPPABLE #-} (IotsType a, Typeable a) => IotsType [a] where
  iotsDefinition = do
    child <- iotsDefinition @a
    let iotsRep = someTypeRep (Proxy @[a])
        iotsOutput = False
        iotsRef = "t.array" <> jsParams (toRef <$> child)
    pure [Node (IotsBuilder {..}) child]

instance  (IotsType a, Typeable a) => IotsType (Set a) where
  iotsDefinition = do
    child <- iotsDefinition @a
    let iotsRep = someTypeRep (Proxy @(Set a))
        iotsOutput = False
        iotsRef = "t.array" <> jsParams (toRef <$> child)
    pure [Node (IotsBuilder {..}) child]

instance IotsType [Char] where
  iotsDefinition = pure [Node (IotsBuilder {..}) []]
    where
      iotsRep = someTypeRep (Proxy @String)
      iotsOutput = False
      iotsRef = "t.string"

-- | Tagging an IOTS Type replaces its ref name.
instance (KnownSymbol s, IotsType a) => IotsType (Tagged s a) where
  iotsDefinition = fmap (fmap rename) <$> iotsDefinition @a
    where
      rename def = def {iotsRef = symbol @s}

------------------------------------------------------------
instance IotsType (HList '[]) where
  iotsDefinition = pure []

instance (IotsType t, IotsType (HList ts)) => IotsType (HList (t ': ts)) where
  iotsDefinition = do
    t <- iotsDefinition @t
    ts <- iotsDefinition @(HList ts)
    pure $ t <> ts

------------------------------------------------------------
class GenericIotsType f where
  genericTypeReps :: SomeTypeRep -> f a -> State Visited (Forest IotsBuilder)

instance (GenericToBody p, Datatype f) => GenericIotsType (D1 f p) where
  genericTypeReps rep d = do
    child <- genericToDef rep d
    let iotsRep = rep
        iotsOutput = False
        iotsRef = repName rep
    pure [Node (IotsBuilder {..}) [child]]

data Cardinality
  = SoleConstructor
  | ManyConstructors

class GenericToDef f where
  genericToDef :: SomeTypeRep -> f a -> State Visited (Tree IotsBuilder)

instance (GenericToBody p, Datatype f) => GenericToDef (D1 f p) where
  genericToDef rep datatype@(M1 constructors) = do
    (childDef, childRefs) <- genericToBody rep constructors
    let moduleName = stringDoc $ Generics.moduleName datatype
        datatypeName = stringDoc $ Generics.datatypeName datatype
        ref = repName rep
        iotsRep = rep
        iotsOutput = True
        iotsRef =
          vsep
            [ "//" <+> moduleName <> "." <> datatypeName
            , "const" <+> ref <+> "=" <+> body <> ";"
            ]
        body =
          case childDef of
            [x] -> x SoleConstructor
            xs  -> "t.union" <> parens (jsArray (apply ManyConstructors <$> xs))
        apply x f = f x
    pure $ Node (IotsBuilder {..}) childRefs

class GenericToBody f where
  genericToBody ::
       SomeTypeRep
    -> f a
    -> State Visited ([Cardinality -> Doc], [Tree IotsBuilder])

instance (Constructor f, GenericToFields p) => GenericToBody (C1 f p) where
  genericToBody rep constructor@(M1 selectors) = do
    (fieldBodies, children) <- genericToFields rep selectors
    let constructorName = stringDoc $ conName constructor
        def SoleConstructor =
          case (conIsRecord constructor, fieldBodies) of
            (False, [])          -> "t.literal" <> parens (squotes constructorName)
            (False, [fieldBody]) -> fieldBody
            (False, _)           -> "t.tuple" <> parens (jsArray fieldBodies)
            (True, _)            -> "t.type" <> parens (jsObject fieldBodies)
        def ManyConstructors =
          case (conIsRecord constructor, fieldBodies) of
            (False, []) -> def SoleConstructor
            _           -> withNamedConstructor (def SoleConstructor)
        withNamedConstructor doc =
          "t.type" <> parens (braces (dquotes constructorName <> ":" <+> doc))
    pure ([def], children)

instance (GenericToBody f, GenericToBody g) => GenericToBody (f :+: g) where
  genericToBody rep _ =
    mappend <$> genericToBody rep (undefined :: f a) <*>
    genericToBody rep (undefined :: g a)

class GenericToFields f where
  genericToFields :: SomeTypeRep -> f a -> State Visited ([Doc], [Tree IotsBuilder])

instance GenericToFields U1 where
  genericToFields _ _ = pure mempty

instance (Selector s, IotsType p, Typeable p) =>
         GenericToFields (S1 s (Rec0 p)) where
  genericToFields _ selector = do
    let childRep = someTypeRep (Proxy @p)
    seen <- gets (Set.member childRep)
    modify (Set.insert childRep)
    child <- iotsDefinition @p
    let fieldRef = foldMap toRef child
        def =
          case selName selector of
            ""   -> fieldRef
            name -> stringDoc name <> ":" <+> fieldRef
    pure $
      if seen
        then ([def], [])
        else ([def], child)

instance (GenericToFields f, GenericToFields g) =>
         GenericToFields (f :*: g) where
  genericToFields rep ~(f :*: g) =
    (<>) <$> genericToFields rep f <*> genericToFields rep g
