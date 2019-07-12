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
    ( HasReps
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
import           GHC.Generics                 ((:*:) ((:*:)), (:+:), C1, Constructor, D1, Datatype, Generic, Generic,
                                               M1 (M1), Rec0, Rep, S1, Selector, U1, conIsRecord, conName, selName)
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
           Seq Doc -> Gather -> State (Set SomeTypeRep) (Seq Doc)
    appendUnseenDefinitions acc Gather {..} = do
        seen <- gets (Set.member gatherRep)
        modify (Set.insert gatherRep)
        pure $
            case (seen, gatherDef) of
                (False, Just _) -> acc |> gatherRef
                _               -> acc

------------------------------------------------------------
type Visited = Set SomeTypeRep

data Gather =
    Gather
        { gatherRep :: SomeTypeRep
        , gatherRef :: Doc
        , gatherDef :: Maybe Doc
        }
    deriving (Show)

gatherReps :: forall a. MyTypeRep a -> State Visited (NonEmpty (Tree Gather))
gatherReps Atom          = pure <$> typeReps (Proxy @a)
gatherReps (Fun from to) = (<>) <$> gatherReps from <*> gatherReps to

treeWalk :: forall a. MyTypeRep a -> State Visited (Tree Gather)
treeWalk Atom = typeReps (Proxy @a)
treeWalk rep@(Fun from to) = do
    lefts <- treeWalk from
    rights <- treeWalk to
    childReps <- gatherReps rep
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
        gatherRep = someTypeRep (Proxy @a)
        gatherDef = Just functionName
        gatherRef =
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
    pure $ Node (Gather {..}) children

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
    typeReps :: a -> State Visited (Tree Gather)
    default typeReps :: (Typeable a, Generic a, GenericHasReps (Rep a)) =>
        a -> State Visited (Tree Gather)
    typeReps = genericTypeReps (someTypeRep (Proxy @a)) . Generics.from

instance HasReps Text where
    typeReps _ = pure $ Node (Gather {..}) []
      where
        gatherRep = someTypeRep (Proxy @Text)
        gatherDef = Nothing
        gatherRef = "t.string"

instance HasReps Char where
    typeReps _ = pure $ Node (Gather {..}) []
      where
        gatherRep = someTypeRep (Proxy @Char)
        gatherDef = Nothing
        gatherRef = "t.string"

instance HasReps Integer where
    typeReps _ = pure $ Node (Gather {..}) []
      where
        gatherRep = someTypeRep (Proxy @Integer)
        gatherDef = Nothing
        gatherRef = "t.Int"

instance HasReps Int where
    typeReps _ = pure $ Node (Gather {..}) []
      where
        gatherRep = someTypeRep (Proxy @Int)
        gatherDef = Nothing
        gatherRef = "t.Int"

instance HasReps a => HasReps (Proxy a) where
    typeReps _ = typeReps (undefined :: a)

instance (HasReps a, HasReps b, Typeable a, Typeable b) => HasReps (a, b) where
    typeReps _ = do
        leftReps <- typeReps (Proxy @a)
        rightReps <- typeReps (Proxy @b)
        let children = [leftReps, rightReps]
            gatherRep = someTypeRep (Proxy @(a, b))
            gatherDef = Nothing
            gatherRef = "t.tuple" <> parens (jsArray (toRef <$> children))
        pure $ Node (Gather {..}) children

instance (HasReps k, HasReps v, Typeable k, Typeable v) =>
         HasReps (Map k v) where
    typeReps _ = do
        keyReps <- typeReps (Proxy @k)
        valueReps <- typeReps (Proxy @v)
        let children = [keyReps, valueReps]
            gatherRep = someTypeRep (Proxy @(Map k v))
            gatherDef = Nothing
            gatherRef = "t.record" <> jsParams (toRef <$> children)
        pure $ Node (Gather {..}) children

instance (HasReps a, Typeable a) => HasReps (Maybe a) where
    typeReps _ = do
        child <- typeReps (Proxy @a)
        let gatherRep = someTypeRep (Proxy @(Maybe a))
            gatherDef = Nothing
            gatherRef = "t.union" <> parens (jsArray [toRef child, "t.null"])
        pure $ Node (Gather {..}) [child]

------------------------------------------------------------
type family IsSpecialListElement a where
    IsSpecialListElement Char = 'True
    IsSpecialListElement a = 'False

instance (ListTypeReps flag a, flag ~ IsSpecialListElement a) =>
         HasReps [a] where
    typeReps _ = listTypeReps (Proxy @flag) (Proxy @a)

class ListTypeReps flag a where
    listTypeReps :: Proxy flag -> Proxy a -> State Visited (Tree Gather)

instance ListTypeReps 'True Char where
    listTypeReps _ _ = pure $ Node (Gather {..}) []
      where
        gatherRep = someTypeRep (Proxy @String)
        gatherDef = Nothing
        gatherRef = "t.string"

instance (HasReps a, Typeable a) => ListTypeReps 'False a where
    listTypeReps _ _ = do
        child <- typeReps (Proxy @a)
        let gatherRep = someTypeRep (Proxy @[a])
            gatherDef = Nothing
            gatherRef = "t.array" <> parens (toRef child)
        pure $ Node (Gather {..}) [child]

------------------------------------------------------------
class GenericHasReps f where
    genericTypeReps :: SomeTypeRep -> f a -> State Visited (Tree Gather)

instance (GenericToBody p, Datatype f) => GenericHasReps (D1 f p) where
    genericTypeReps rep d = do
        child <- genericToDef rep d
        let gatherRep = rep
            gatherDef = Nothing
            gatherRef = repName rep
        pure $ Node (Gather {..}) [child]

class GenericToDef f where
    genericToDef :: SomeTypeRep -> f a -> State Visited (Tree Gather)

instance (GenericToBody p, Datatype f) => GenericToDef (D1 f p) where
    genericToDef rep datatype@(M1 constructors) = do
        (childDef, childRefs) <- genericToBody rep constructors
        let gatherRep = rep
            moduleName = stringDoc $ Generics.moduleName datatype
            datatypeName = stringDoc $ Generics.datatypeName datatype
            body =
                case childDef of
                    [x] -> x SoleConstructor
                    xs ->
                        "t.union" <>
                        parens (jsArray (($ ManyConstructors) <$> xs))
            gatherRef =
                vsep
                    [ "//" <+> moduleName <> "." <> datatypeName
                    , "const" <+> ref <+> "=" <+> body <> ";"
                    ]
            gatherDef = Just ref
            ref = repName rep
        pure $ Node (Gather {..}) childRefs

class GenericToBody f where
    genericToBody ::
           SomeTypeRep
        -> f a
        -> State Visited ([Cardinality -> Doc], [Tree Gather])

data Cardinality
    = SoleConstructor
    | ManyConstructors

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
    genericToFields ::
           SomeTypeRep -> f a -> State Visited ([Doc], [Tree Gather])

instance GenericToFields U1 where
    genericToFields _ _ = pure ([], [])

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
        mappend <$> genericToFields rep f <*> genericToFields rep g

------------------------------------------------------------
repName :: SomeTypeRep -> Doc
repName = stringDoc . fold . go
  where
    go :: SomeTypeRep -> [String]
    go rep@(SomeTypeRep someRep)
        | rep == R.someTypeRep (Proxy @String) = ["String"]
        | otherwise =
            let (tyCon, params) = R.splitApps someRep
                headName =
                    case R.tyConName tyCon of
                        "[]"  -> "List"
                        other -> other
             in headName : foldMap go params

toRef :: Tree Gather -> Doc
toRef = gatherRef . rootLabel

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
