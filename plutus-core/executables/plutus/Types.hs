{-# LANGUAGE TypeFamilyDependencies #-}
-- all following needed for singletons-th
{-# OPTIONS_GHC -fno-warn-redundant-constraints #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE DataKinds #-}
module Types where

import PlutusCore.Default
import PlutusCore qualified as PLC
import PlutusIR qualified as PIR
import UntypedPlutusCore qualified as UPLC

import Control.Lens
import Data.Singletons.TH
import Prettyprinter

data Naming = Name
            | DeBruijn
            | NamedDeBruijn
            deriving stock (Eq, Show)

data Ann = Unit
         | SrcSpan_
         -- MAYBE: | Coverage
         -- MAYBE: | Provenance
         deriving stock (Eq, Show)

data Lang = Pir { _naming :: Naming, _ann :: Ann }
          | Plc { _naming :: Naming, _ann :: Ann }
          | Uplc { _naming :: Naming, _ann :: Ann }
          | Data -- FIXME: naming,ann partial for data
          deriving stock (Eq, Show)
makeLenses ''Lang

data Format = Text
            | Flat_
            | Cbor
            | Json
            deriving stock (Show)

-- untyped
data FileType = FileType
    { _fFormat :: Format
    , _fLang :: Lang
    }
    deriving stock (Show)
makeLenses ''FileType

-- TODO: in-filenames should be typed separately than out-filenames
data FileName = AbsolutePath FilePath
              | Example ExampleName
              | StdIn
              | StdOut
              deriving stock (Eq, Show)

type ExampleName = String

-- tagged by the lang
data File (l :: Lang) = File
    { _fType :: FileType
    , _fName :: FileName
    }
    deriving stock (Show)
makeLenses ''File

data OptimiseLvl = NoOptimise
                 | SafeOptimise
                 | UnsafeOptimise
                 deriving stock (Show)

data Mode = Compile
          | Run
          | Bench Secs
          | Debug FilePath -- ^ the tx dir
          | PrintBuiltins
          | ListExamples
          | Help
          | Version
          deriving stock (Show)

type Secs = Int
type MemBudget = Int
type CpuBudget = Int
data Budget = Budget CpuBudget MemBudget
    deriving stock (Show)

data PrettyStyle = None
                 | Classic
                 | ClassicDebug
                 | Readable
                 | ReadableDebug
                 deriving stock (Show)

data Verbosity = VNone
               | VDefault
               | VFull
               deriving stock (Eq, Show)

-- SINGLETONS-related

genSingletons [''Ann, ''Naming, ''Lang]
singDecideInstances [''Ann, ''Naming, ''Lang]

-- the dependent pairs
data SomeFile = forall s. SomeFile (SLang s) (File s)
data SomeAst = forall s. SomeAst (SLang s) (FromLang s)

-- the way to go from a runtime value to the dependent pair
mkSomeFile :: FileType -> FileName -> SomeFile
mkSomeFile ft fn =
    -- Note to self: beware of let bindings here because of
    -- MonomorphismRestriction + MonoLocalBinds (implied by GADTs/TypeFamilies)
    case toSing (ft^.fLang) of
        SomeSing sng -> SomeFile sng (File ft fn)

type family FromLang (lang :: Lang) = result | result -> lang where
    FromLang ('Pir n a) = PIR.Program (FromNameTy n) (FromName n) DefaultUni DefaultFun (FromAnn a)
    FromLang ('Plc n a) = PLC.Program (FromNameTy n) (FromName n) DefaultUni DefaultFun (FromAnn a)
    FromLang ('Uplc n a) = UPLC.UnrestrictedProgram (FromName n) DefaultUni DefaultFun (FromAnn a)

type family FromName (naming :: Naming) = result | result -> naming where
    FromName 'Name = PLC.Name
    FromName 'DeBruijn = PLC.DeBruijn
    FromName 'NamedDeBruijn = PLC.NamedDeBruijn

type family FromNameTy (naming :: Naming) = result | result -> naming where
    FromNameTy 'Name = PLC.TyName
    FromNameTy 'DeBruijn = PLC.TyDeBruijn
    FromNameTy 'NamedDeBruijn = PLC.NamedTyDeBruijn

type family FromAnn (ann :: Ann) = result | result -> ann where
    FromAnn 'Unit = ()
    FromAnn 'SrcSpan_ = PLC.SrcSpan

instance Show SomeFile where
    show (SomeFile _ f) = show f

instance Pretty SomeFile where
    pretty = viaShow

instance Pretty (File l) where
    pretty = viaShow

instance Pretty Lang where
    pretty = viaShow
