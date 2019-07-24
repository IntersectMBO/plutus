{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE DefaultSignatures     #-}
{-# LANGUAGE DerivingStrategies    #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NamedFieldPuns        #-}
{-# LANGUAGE OverloadedLists       #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE PatternSynonyms       #-}
{-# LANGUAGE PolyKinds             #-}
{-# LANGUAGE RecordWildCards       #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE UndecidableInstances  #-}

module Schema.IOTS
    ( HasReps(typeReps)
    , MyTypeable
    , render
    , export
    ) where

import           Control.Monad.Fix            (fix)
import           Control.Monad.State          (State, evalState, gets, modify)
import           Data.Foldable                (fold, foldlM, toList)
import           Data.List.NonEmpty           (NonEmpty)
import qualified Data.List.NonEmpty           as NEL
import           Data.Map                     (Map)
import           Data.Proxy                   (Proxy (Proxy))
import           Data.Sequence                (Seq, (<|), (|>))
import           Data.Set                     (Set)
import qualified Data.Set                     as Set
import           Data.Text                    (Text)
import qualified Data.Text                    as Text
import           Data.Tree                    (Tree (Node), rootLabel, subForest)
import           GHC.Exts                     (RuntimeRep, TYPE)
import           GHC.Generics                 ((:*:) ((:*:)), (:+:), C1, Constructor, D1, Datatype, Generic, M1 (M1),
                                               Rec0, Rep, S1, Selector, U1, conIsRecord, conName, selName)
import qualified GHC.Generics                 as Generics
import           Text.PrettyPrint.Leijen.Text (Doc, braces, brackets, char, comma, displayTStrict, dquotes, indent,
                                               linebreak, parens, punctuate, renderPretty, space, squotes, textStrict,
                                               vsep, (<+>))
import           Type.Reflection              (SomeTypeRep (SomeTypeRep), Typeable, someTypeRep)
import qualified Type.Reflection              as R

-- We need a list of arguments to a function: Typeable
-- We need to give a unique name to each concrete type: Typeable
-- We need to take an argument and turn it into a definition: Generics.
-- So...how do we go from a TypeRep to a (from (Proxy @a))? Is the answer indexed typereps from Type.Reflection?
{-# ANN module ("HLint: ignore Avoid restricted function" :: Text)
        #-}

------------------------------------------------------------
preamble :: Doc
preamble = "import * as t from 'io-ts'"

export ::
       forall a. (MyTypeable a)
    => a
    -> Doc
export _ = vsep . punctuate linebreak . toList $ preamble <| definitions
  where
    definitions :: Seq Doc
    definitions =
        flip evalState Set.empty . depthfirstM appendUnseenDefinitions [] $
        flip evalState Set.empty . treeWalk $ myTypeRep @a
    appendUnseenDefinitions ::
           Seq Doc -> Iots -> State (Set SomeTypeRep) (Seq Doc)
    appendUnseenDefinitions acc Iots {..} = do
        seen <- gets (Set.member iotsRep)
        modify (Set.insert iotsRep)
        pure $
            if iotsOutput && not seen
                then acc |> iotsRef
                else acc

------------------------------------------------------------
type Visited = Set SomeTypeRep

data Iots =
    Iots
        { iotsRep    :: SomeTypeRep
        -- ^ The type this record describes.
        , iotsRef    :: Doc
        -- ^ How we refer to this type. For IOTS builtins this is
        -- probably `t.something`. For our definitions it will the the
        -- type name (eg. `User`).
        , iotsOutput :: Bool
        -- ^ Should we write this type out in the final export?
        }
    deriving (Show)

iotsReps :: forall a. MyTypeRep a -> State Visited (NonEmpty (Tree Iots))
iotsReps Atom          = pure <$> typeReps (Proxy @a)
iotsReps (Fun from to) = (<>) <$> iotsReps from <*> iotsReps to

treeWalk :: forall a. MyTypeRep a -> State Visited (Tree Iots)
treeWalk Atom = typeReps (Proxy @a)
treeWalk rep@(Fun from to) = do
    lefts <- treeWalk from
    rights <- treeWalk to
    childReps <- iotsReps rep
    let children = lefts : subForest rights
        typeSignature =
            (if NEL.length childReps == 1
                 then mempty
                 else (jsParams $ labelledParameters (NEL.init childReps)) <>
                      space) <>
            "=>" <+>
            toRef (NEL.last childReps)
        labelledParameters = zipWith labelledParameter (char <$> ['a' .. 'z'])
        labelledParameter name tree = name <> ":" <+> toRef tree
        iotsRep = someTypeRep (Proxy @a)
        iotsOutput = True
        iotsRef =
            "class" <+>
            "Type" <+>
            braces
                (inset
                     ("constructor" <>
                      parens
                          (inset
                               ("readonly" <+>
                                functionName <> ":" <+> typeSignature)) <+>
                      braces mempty))
        functionName = "someFunction" -- TODO Wrong
    pure $ Node (Iots {..}) children

------------------------------------------------------------
-- Create our own universe of types.
data MyTypeRep (a :: k) where
    Atom
        :: forall (a :: *). (Typeable a, HasReps a)
        => MyTypeRep a
    Fun
        :: forall (r1 :: RuntimeRep) (r2 :: RuntimeRep) (a :: TYPE r1) (b :: TYPE r2).
           Typeable (a -> b)
        => MyTypeRep a
        -> MyTypeRep b
        -> MyTypeRep (a -> b)

------------------------------------------------------------
class MyTypeable a where
    myTypeRep :: MyTypeRep a

instance forall (a :: *). (Typeable a, HasReps a) => MyTypeable a where
    myTypeRep = Atom @a

instance {-# OVERLAPPING #-} forall a b. ( MyTypeable a
                                         , MyTypeable b
                                         , Typeable (a -> b)
                             ) =>
                             MyTypeable ((->) a b) where
    myTypeRep = Fun myTypeRep myTypeRep

------------------------------------------------------------
class HasReps a where
    typeReps :: a -> State Visited (Tree Iots)
    default typeReps :: (Typeable a, Generic a, GenericHasReps (Rep a)) =>
        a -> State Visited (Tree Iots)
    typeReps = genericTypeReps (someTypeRep (Proxy @a)) . Generics.from

instance HasReps Text where
    typeReps _ = pure $ Node (Iots {..}) []
      where
        iotsRep = someTypeRep (Proxy @Text)
        iotsOutput = False
        iotsRef = "t.string"

instance HasReps Char where
    typeReps _ = pure $ Node (Iots {..}) []
      where
        iotsRep = someTypeRep (Proxy @Char)
        iotsOutput = False
        iotsRef = "t.string"

instance HasReps Integer where
    typeReps _ = pure $ Node (Iots {..}) []
      where
        iotsRep = someTypeRep (Proxy @Integer)
        iotsOutput = False
        iotsRef = "t.Int"

instance HasReps Int where
    typeReps _ = pure $ Node (Iots {..}) []
      where
        iotsRep = someTypeRep (Proxy @Int)
        iotsOutput = False
        iotsRef = "t.Int"

instance HasReps a => HasReps (Proxy a) where
    typeReps _ = typeReps (undefined :: a)

instance (HasReps a, HasReps b, Typeable a, Typeable b) => HasReps (a, b) where
    typeReps _ = do
        leftReps <- typeReps (Proxy @a)
        rightReps <- typeReps (Proxy @b)
        let children = [leftReps, rightReps]
            iotsRep = someTypeRep (Proxy @(a, b))
            iotsOutput = False
            iotsRef = "t.tuple" <> parens (jsArray (toRef <$> children))
        pure $ Node (Iots {..}) children

instance (HasReps k, HasReps v, Typeable k, Typeable v) =>
         HasReps (Map k v) where
    typeReps _ = do
        keyReps <- typeReps (Proxy @k)
        valueReps <- typeReps (Proxy @v)
        let children = [keyReps, valueReps]
            iotsRep = someTypeRep (Proxy @(Map k v))
            iotsOutput = False
            iotsRef = "t.record" <> jsParams (toRef <$> children)
        pure $ Node (Iots {..}) children

instance HasReps () where
    typeReps _ = do
        let iotsRep = someTypeRep (Proxy @())
            iotsOutput = False
            iotsRef = "t.null"
        pure $ Node (Iots {..}) []

instance (HasReps a, Typeable a) => HasReps (Maybe a) where
    typeReps _ = do
        aChildren <- typeReps (Proxy @a)
        nothingChildren <- typeReps (Proxy @())
        let children = [aChildren, nothingChildren]
            iotsRep = someTypeRep (Proxy @(Maybe a))
            iotsOutput = False
            iotsRef = "t.union" <> parens (jsArray (toRef <$> children))
        pure $ Node (Iots {..}) children

------------------------------------------------------------
type family IsSpecialListElement a where
    IsSpecialListElement Char = 'True
    IsSpecialListElement a = 'False

instance (ListTypeReps flag a, flag ~ IsSpecialListElement a) =>
         HasReps [a] where
    typeReps _ = listTypeReps (Proxy @flag) (Proxy @a)

class ListTypeReps flag a where
    listTypeReps :: Proxy flag -> Proxy a -> State Visited (Tree Iots)

instance ListTypeReps 'True Char where
    listTypeReps _ _ = pure $ Node (Iots {..}) []
      where
        iotsRep = someTypeRep (Proxy @String)
        iotsOutput = False
        iotsRef = "t.string"

instance (HasReps a, Typeable a) => ListTypeReps 'False a where
    listTypeReps _ _ = do
        child <- typeReps (Proxy @a)
        let iotsRep = someTypeRep (Proxy @[a])
            iotsOutput = False
            iotsRef = "t.array" <> parens (toRef child)
        pure $ Node (Iots {..}) [child]

------------------------------------------------------------
class GenericHasReps f where
    genericTypeReps :: SomeTypeRep -> f a -> State Visited (Tree Iots)

instance (GenericToBody p, Datatype f) => GenericHasReps (D1 f p) where
    genericTypeReps rep d = do
        child <- genericToDef rep d
        let iotsRep = rep
            iotsOutput = False
            iotsRef = repName rep
        pure $ Node (Iots {..}) [child]

data Cardinality
    = SoleConstructor
    | ManyConstructors

class GenericToDef f where
    genericToDef :: SomeTypeRep -> f a -> State Visited (Tree Iots)

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
                    xs ->
                        "t.union" <>
                        parens (jsArray (($ ManyConstructors) <$> xs))
        pure $ Node (Iots {..}) childRefs

class GenericToBody f where
    genericToBody ::
           SomeTypeRep
        -> f a
        -> State Visited ([Cardinality -> Doc], [Tree Iots])

instance (Constructor f, GenericToFields p) => GenericToBody (C1 f p) where
    genericToBody rep constructor@(M1 selectors) = do
        (fieldBodies, children) <- genericToFields rep selectors
        let constructorName = stringDoc $ conName constructor
            def SoleConstructor =
                case (conIsRecord constructor, fieldBodies) of
                    (False, []) ->
                        "t.literal" <> parens (squotes constructorName)
                    (False, [fieldBody]) -> fieldBody
                    (False, _) -> "t.tuple" <> parens (jsArray fieldBodies)
                    (True, _) -> "t.type" <> parens (jsObject fieldBodies)
            def ManyConstructors =
                case (conIsRecord constructor, fieldBodies) of
                    (False, []) -> def SoleConstructor
                    _           -> withNamedConstructor (def SoleConstructor)
            withNamedConstructor doc =
                "t.type" <>
                parens (braces (dquotes constructorName <> ":" <+> doc))
        pure ([def], children)

instance (GenericToBody f, GenericToBody g) => GenericToBody (f :+: g) where
    genericToBody rep _ =
        mappend <$> genericToBody rep (undefined :: f a) <*>
        genericToBody rep (undefined :: g a)

class GenericToFields f where
    genericToFields :: SomeTypeRep -> f a -> State Visited ([Doc], [Tree Iots])

instance GenericToFields U1 where
    genericToFields _ _ = pure mempty

instance (Selector s, HasReps p, Typeable p) =>
         GenericToFields (S1 s (Rec0 p)) where
    genericToFields _ selector = do
        let childRep = someTypeRep (Proxy @p)
        seen <- gets (Set.member childRep)
        modify (Set.insert childRep)
        child <- typeReps (Proxy @p)
        let fieldRef = toRef child
            def =
                case selName selector of
                    ""   -> fieldRef
                    name -> stringDoc name <> ":" <+> fieldRef
        pure $
            if seen
                then ([def], [])
                else ([def], [child])

instance (GenericToFields f, GenericToFields g) =>
         GenericToFields (f :*: g) where
    genericToFields rep ~(f :*: g) =
        (<>) <$> genericToFields rep f <*> genericToFields rep g

------------------------------------------------------------
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

toRef :: Tree Iots -> Doc
toRef = iotsRef . rootLabel

------------------------------------------------------------
depthfirstM ::
       Monad m => (Seq b -> a -> m (Seq b)) -> Seq b -> Tree a -> m (Seq b)
depthfirstM f =
    fix $ \rec acc (Node root leaves)
        -- Fold the leaves first.
     -> do
        children <- foldlM rec acc leaves
        -- Deal with the root last.
        f children root

------------------------------------------------------------
render :: Doc -> Text
render = displayTStrict . renderPretty 0.8 200

stringDoc :: String -> Doc
stringDoc = textStrict . Text.pack

indentedList :: [Doc] -> Doc
indentedList = inset . vsep . punctuate comma

inset :: Doc -> Doc
inset doc = linebreak <> indent 4 doc <> linebreak

jsArray :: [Doc] -> Doc
jsArray = brackets . indentedList

jsObject :: [Doc] -> Doc
jsObject = braces . indentedList

jsParams :: [Doc] -> Doc
jsParams = parens . indentedList
