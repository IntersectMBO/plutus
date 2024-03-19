.. highlight:: haskell
.. _exporting_a_blueprint:

How to produce a Plutus Contract Blueprint (CIP-57)
===================================================

`CIP-0057`_ Plutus Contract Blueprints are used to document the binary interface of a
Plutus contract in a machine-readable format (JSON schema).

A contract Blueprint can be produced by using the
`writeBlueprint` function exported by the `PlutusTx.Blueprint` module::

   writeBlueprint
     :: FilePath
     -- ^ The file path where the blueprint will be written to,
     --  e.g. '/tmp/plutus.json'
     -> ContractBlueprint
     -- ^ Contains all the necessary information to generate 
     -- a blueprint for a Plutus contract.
     -> IO ()

In order to demonstrate the usage of the `writeBlueprint` function,
Let's consider the following example validator function and its interface::

  data MyParams = MyParams
    { myBool    :: Bool
    , myInteger :: Integer
    }
    deriving stock (Generic)
    deriving anyclass (AsDefinitionId)

  $(PlutusTx.makeLift ''Params)
  $(makeIsDataSchemaIndexed ''Params [('MkParams, 0)])
    
  type MyDatum = Integer

  type MyRedeemer = ()

  typedValidator :: MyParams -> MyDatum -> MyRedeemer -> ScriptContext -> Bool
  typedValidator datum redeemer scriptContext = ... 

  untypedValidator :: MyParams -> BuiltinData -> BuiltinData -> BuiltinData -> ()
  untypedValidator params datum redeemer _scriptContext =
    check $ typedValidator
      params
      (unsafeFromBuiltinData datum)
      (unsafeFromBuiltinData redeemer)

First of all we need to import required functionality::

  import PlutusTx.Blueprint
    ( ContractBlueprint (..)
    , Preamble (..)
    , Purpose (..)
    , ValidatorBlueprint (..)
    , ArgumentBlueprint (..)
    , ParameterBlueprint (..)
    , AsDefinitionId (..)
    , definitionRef
    , deriveDefinitions
    )
  import PlutusTx.Blueprint.TH (makeIsDataSchemaIndexed) 

Next we define a contract blueprint value of the following type:

.. code-block:: haskell

  data ContractBlueprint where
    MkContractBlueprint ::
      forall referencedTypes.
      { contractId :: Maybe Text
      -- ^ An optional identifier for the contract.
      , contractPreamble :: Preamble
      -- ^ An object with meta-information about the contract.
      , contractValidators :: Set (ValidatorBlueprint referencedTypes)
      -- ^ A set of validator blueprints that are part of the contract.
      , contractDefinitions :: Definitions referencedTypes
      -- ^ A registry of schema definitions used across the blueprint.
      } -> ContractBlueprint

.. note::

    The 'referencedTypes' type parameter is used to track the types used in the contract
    making sure their schemas are included in the blueprint and that they are referenced
    in a type-safe way.

    The blueprint will contain JSON schema definitions for all the types used in the contract,
    including the types **nested** within the top-level types (`MyParams`, `MyDatum`, `MyRedeemer`):

    * ``Integer`` - nested within `MyDatum` and `MyParams`.
    * ``Bool`` - nested within `MyParams`.
    * ``()`` - nested within `MyRedeemer`.

    This way, the `referencedTypes` type variable is inferred to be the following list:

    .. code-block:: haskell
      
      '[ MyParams    -- top-level type
       , MyDatum     -- top-level type
       , MyRedeemer  -- top-level type 
       , Integer     -- nested type
       , Bool        -- nested type
       , ()          -- nested type
       ]

We can construct a value of this type like in this::
  
  myContractBlueprint :: ContractBlueprint 
  myContractBlueprint = MkContractBlueprint
    { contractId = Just "my-contract"
    , contractPreamble = myPreamble -- defined below
    , contractValidators = Set.singleton myValidator -- defined below
    , contractDefinitions = deriveDefinitions @[MyParams, MyDatum, MyRedeemer]
    }

The `contractId` field is optional and can be used to give a unique identifier to the contract.  

The `contractPreamble` field is a value of type `PlutusTx.Blueprint.Preamble` 
contains a meta-information about the contract:

.. code-block:: haskell

  data Preamble = MkPreamble
    { preambleTitle         :: Text
    -- ^ A short and descriptive title of the contract application
    , preambleDescription   :: Maybe Text
    -- ^ A more elaborate description
    , preambleVersion       :: Text
    -- ^ A version number for the project.
    , preamblePlutusVersion :: PlutusVersion
    -- ^ The Plutus version assumed for all validators
    , preambleLicense       :: Maybe Text
    -- ^ A license under which the specification
    -- and contract code is distributed
    }

Here is an example construction::

  myPreamble :: Preamble
  myPreamble = MkPreamble
    { preambleTitle = "My Contract"
    , preambleDescription = Just "A simple contract"
    , preambleVersion = "1.0.0"
    , preamblePlutusVersion = PlutusV2
    , preambleLicense = Just "MIT"
    }

The ``contractDefinitions`` field is a registry of schema definitions used across the blueprint.
It can be constructed using the ``deriveDefinitions`` function which automatically
constructs schema definitions for all the types its applied to inluding the types
nested within them.

Since every type in the ``referencedTypes`` list is going to have its derived JSON-schema in the
``contractDefinitions`` registry under a certain unique ``DefinitionId`` key, we need to make sure
that it has:

* an instance of the ``GHC.Generics.Generic`` type class::

    {-# LANGUAGE DerivingStrategies, StandaloneDeriving, DeriveGeneric #-}
    deriving instance stock Generic MyParams

* an instance of the ``AsDefinitionId`` type class. Most of the times it could be derived
  generically with the ``anyclass`` strategy, for example::

    {-# LANGUAGE DerivingStrategies, StandaloneDeriving, DeriveAnyClass #-}
    deriving instance anyclass AsDefinitionId MyParams
    
* an instance of the ``HasSchema`` type class. If your validator exposes standard supported types
  like ``Integer`` or ``Bool`` you don't need to define this instance. If your validator uses
  custom types then you should be deriving it using the ``makeIsDataSchemaIndexed`` Template Haskell function,
  which derives it alongside with the corresponding `ToBuiltinData`/`FromBuiltinData` instances,
  for example::

    {-# LANGUAGE TemplateHaskell #-}
    $(makeIsDataSchemaIndexed ''MyDatum [('MkMyDatum, 0)])


Finally, we need to define a validator blueprint for each validator used in the contract.

Our contract can contain one or more validators and for each one we need to provide
a description as a value of the following type::

  data ValidatorBlueprint (referencedTypes :: [Type]) = MkValidatorBlueprint
    { validatorTitle        :: Text
    -- ^ A short and descriptive name for the validator.
    , validatorDescription  :: Maybe Text
    -- ^ An informative description of the validator.
    , validatorRedeemer     :: ArgumentBlueprint referencedTypes
    -- ^ A description of the redeemer format expected by this validator.
    , validatorDatum        :: Maybe (ArgumentBlueprint referencedTypes)
    -- ^ A description of the datum format expected by this validator.
    , validatorParameters   :: Maybe (NonEmpty (ParameterBlueprint referencedTypes))
    -- ^ A list of parameters required by the script.
    , validatorCompiledCode :: Maybe ByteString
    -- ^ A full compiled and CBOR-encoded serialized flat script.
    }

In our example this would be::

  myValidator = MkValidatorBlueprint
    { validatorTitle = "My Validator"
    , validatorDescription = Just "An example validator"
    , validatorParameters =
        [ MkParameterBlueprint
          { parameterTitle = Just "My Validator Parameters"
          , parameterDescription = Just "Parameters configure the validator in compile-time"
          , parameterPurpose = Set.singleton Spend
          , parameterSchema = definitionRef @MyParams
          }
        ]
    , validatorRedeemer =
        MkArgumentBlueprint
          { argumentTitle = Just "My Redeemer"
          , argumentDescription = Just "A redeemer that does something awesome"
          , argumentPurpose = Set.fromList [Spend, Mint]
          , argumentSchema = definitionRef @MyRedeemer
          }
    , validatorDatum = Just
        MkArgumentBlueprint
          { argumentTitle = Just "My Datum"
          , argumentDescription = Just "A datum that contains something awesome"
          , argumentPurpose = Set.singleton Spend
          , argumentSchema = definitionRef @MyDatum
          }
    , validatorCompiledCode = Nothing -- you can optionally provide the compiled code here
    }

The ``definitionRef`` function is used to reference a schema definition of a given type. It is 
smart enough to discover the schema definition from the ``referencedType`` list and 
fails to compile if the referenced type is not included.

With all the pieces in place, we can now write the blueprint to a file::

  writeBlueprint "/tmp/plutus.json" myContractBlueprint

Annotations
-----------

Any `CIP-0057`_ blueprint type definition may include `optional keywords`_ to provide
additional information:

* title
* description
* $comment

Its possible to add these keywords to a Blueprint type definition by annotating the
Haskell type from which its derived with a corresponding annotation:

* ``SchemaTitle`` 
* ``SchemaDescription``
* ``SchemaComment``

For example, to add a title and description to the ``MyParams`` type,
we can use the ``SchemaTitle`` and ``SchemaDescription`` annotations::

  {-# ANN type MyParams (SchemaTitle "Title for the MyParams definition") #-}
  {-# ANN type MyParams (SchemaDescription "Description for the MyParams definition") #-}
  data MyParams = MyParams { myBool :: Bool, myInteger :: Integer }

results in the following JSON schema definition:

.. code-block:: json

  {
    "title": "Title for the MyParams definition",
    "description": "Description for the MyParams definition",
    "dataType": "constructor",
    "fields": [
      { "$ref": "#/definitions/Bool" },
      { "$ref": "#/definitions/Integer" }
    ],
    "index": 0
  }

For sum-types its possible to annotate constructors::

  {-# ANN R1 (SchemaComment "Left" ) #-}
  {-# ANN R2 (SchemaComment "Right") #-}
  data MyRedeemer = R1 | R2

to produce the JSON schema definition:

.. code-block:: json

  {
    "oneOf": [
      {
        "$comment": "Left",
        "dataType": "constructor",
        "fields": [],
        "index": 0
      },
      {
        "$comment": "Right",
        "dataType": "constructor",
        "fields": [],
        "index": 1
      }
    ]
  }

.. note::
  You can find a more elaborate example of a contract blueprint in the ``Blueprint.Tests``
  module of the plutus repository.

.. _CIP-0057: https://cips.cardano.org/cip/CIP-0057
.. _optional keywords: https://cips.cardano.org/cip/CIP-0057#for-any-data-type
