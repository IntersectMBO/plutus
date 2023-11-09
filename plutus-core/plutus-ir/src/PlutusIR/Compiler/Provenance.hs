-- editorconfig-checker-disable-file
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}
-- | Module handling provenances of terms.
module PlutusIR.Compiler.Provenance where

import PlutusIR

import PlutusCore.Pretty qualified as PLC

import Data.Set qualified as S
import Prettyprinter ((<+>))
import Prettyprinter qualified as PP

-- | Indicates where a value comes from.
--
-- This is either an original annotation or a pieces of context explaining how the term
-- relates to a previous 'Provenance'. We also provide 'noProvenance' for convenience.
--
-- The provenance should always be just the original annotation, if we have one. It should only be another
-- kind of provenance if we're in the process of generating some term that doesn't correspond directly to a term in
-- the original AST.
data Provenance a = Original a
                  | LetBinding Recursivity (Provenance a)
                  | TermBinding String (Provenance a)
                  | TypeBinding String (Provenance a)
                  | DatatypeComponent DatatypeComponent (Provenance a)
                  -- | Added for accumulating difference provenances when floating lets
                  | MultipleSources (S.Set (Provenance a))
                  deriving stock (Show, Eq, Ord, Foldable)

instance Ord a => Semigroup (Provenance a) where
    x <> y = MultipleSources (toSet x `S.union` toSet y)
      where
        toSet = \case
            MultipleSources ps -> ps
            other              -> S.singleton other

instance Ord a => Monoid (Provenance a) where
    mempty = noProvenance

-- workaround, use a smart constructor to replace the older NoProvenance data constructor
noProvenance :: Provenance a
noProvenance = MultipleSources S.empty

data DatatypeComponent = Constructor
                       | ConstructorType
                       | Destructor
                       | DestructorType
                       | DatatypeType
                       | PatternFunctor
                       deriving stock (Show, Eq, Ord)

instance PP.Pretty DatatypeComponent where
    pretty = \case
        Constructor     -> "constructor"
        ConstructorType -> "constructor type"
        Destructor      -> "destructor"
        DestructorType  -> "destructor type"
        DatatypeType    -> "datatype type"
        PatternFunctor  -> "pattern functor"

data GeneratedKind = RecursiveLet
    deriving stock (Show, Eq)

instance PP.Pretty GeneratedKind where
    pretty = \case
        RecursiveLet -> "recursive let"

-- | Set the provenance on a term to the given value.
setProvenance :: Functor f => Provenance b -> f a -> f (Provenance b)
setProvenance = (<$)

-- | Mark all the annotations on a term as original. Useful for preparing terms for the PIR compiler.
original :: Functor f => f a -> f (Provenance a)
original = fmap Original

instance PP.Pretty a => PP.Pretty (Provenance a) where
    pretty = \case
        DatatypeComponent c p -> PP.pretty c <> ";" <+> "from" <+> PLC.pretty p
        Original p -> PLC.pretty p
        LetBinding r p ->
            let
                rstr = case r of
                    NonRec -> "non-recursive"
                    Rec    -> "recursive"
            in "(" <> rstr <> ")" <+> "let binding" <> ";" <+> "from" <+> PLC.pretty p
        TermBinding n p -> "term binding" <+> "of" <+> PLC.pretty n <> ";" <+> "from" <+> PLC.pretty p
        TypeBinding n p -> "type binding" <+> "of" <+> PLC.pretty n <> ";" <+> "from" <+> PLC.pretty p
        MultipleSources p1 -> case S.toList p1 of
                                [] -> "<unknown>"
                                l  -> PLC.prettyList l
