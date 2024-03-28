.. highlight:: haskell
.. _exporting_a_blueprint:

How to produce a Plutus Contract Blueprint (CIP-57)
---------------------------------------------------
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
Let's consider the following example validator function and its interface:

.. literalinclude:: Cip57Blueprint.hs
   :start-after: BEGIN interface types
   :end-before:  END interface types

.. literalinclude:: Cip57Blueprint.hs
   :start-after: BEGIN validator
   :end-before:  END validator

First of all we need to import required functionality:

.. literalinclude:: Cip57Blueprint.hs
   :start-after: BEGIN imports
   :end-before:  END imports

Next we define a contract blueprint value of the following type:

.. code-block:: haskell

  data ContractBlueprint where
    MkContractBlueprint
      :: forall referencedTypes
      . { contractId :: Maybe Text
          -- ^ An optional identifier for the contract.
        , contractPreamble :: Preamble
          -- ^ An object with meta-information about the contract.
        , contractValidators :: Set (ValidatorBlueprint referencedTypes)
          -- ^ A set of validator blueprints that are part of the contract.
        , contractDefinitions :: Definitions referencedTypes
          -- ^ A registry of schema definitions used across the blueprint.
        }
      -> ContractBlueprint

.. note::

    The 'referencedTypes' type parameter is used to track the types used in the contract
    making sure their schemas are included in the blueprint and that they are referenced
    in a type-safe way.

    The blueprint will contain JSON schema definitions for all the types used in the contract,
    including the types **nested** within the top-level types (`MyParams`, `MyDatum`, `MyRedeemer`):

    * ``Integer`` - nested within `MyDatum` and `MyParams`.
    * ``Bool`` - nested within `MyParams`.

    This way, the `referencedTypes` type variable is inferred to be the following list:

    .. code-block:: haskell
      
      '[ MyParams    -- top-level type
       , MyDatum     -- top-level type
       , MyRedeemer  -- top-level type 
       , Integer     -- nested type
       , Bool        -- nested type
       ]

We can construct a value of this type like in this:
  
.. literalinclude:: Cip57Blueprint.hs
   :start-after: BEGIN contract blueprint declaration
   :end-before:  END contract blueprint declaration

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

Here is an example construction:

.. literalinclude:: Cip57Blueprint.hs
   :start-after: BEGIN preamble declaration
   :end-before:  END preamble declaration

The ``contractDefinitions`` field is a registry of schema definitions used across the blueprint.
It can be constructed using the ``deriveDefinitions`` function which automatically
constructs schema definitions for all the types its applied to inluding the types
nested within them.

Since every type in the ``referencedTypes`` list is going to have its derived JSON-schema in the
``contractDefinitions`` registry under a certain unique ``DefinitionId`` key, we need to make sure
that it has:

* an instance of the ``GHC.Generics.Generic`` type class:

  .. literalinclude:: Cip57Blueprint.hs
     :start-after: BEGIN generic instances
     :end-before:  END generic instances

* an instance of the ``AsDefinitionId`` type class. Most of the times it could be derived
  generically with the ``anyclass`` strategy, for example:

  .. literalinclude:: Cip57Blueprint.hs
     :start-after: BEGIN AsDefinitionId instances
     :end-before:  END AsDefinitionId instances
    
* an instance of the ``HasSchema`` type class. If your validator exposes standard supported types
  like ``Integer`` or ``Bool`` you don't need to define this instance. If your validator uses
  custom types then you should be deriving it using the ``makeIsDataSchemaIndexed`` Template Haskell function,
  which derives it alongside with the corresponding `ToBuiltinData`/`FromBuiltinData` instances,
  for example:

  .. literalinclude:: Cip57Blueprint.hs
     :start-after: BEGIN makeIsDataSchemaIndexed MyParams
     :end-before:  END makeIsDataSchemaIndexed MyParams

Finally, we need to define a validator blueprint for each validator used in the contract.

Our contract can contain one or more validators and for each one we need to provide
a description as a value of the following type:

  .. code-block:: haskell

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

In our example this would be:

.. literalinclude:: Cip57Blueprint.hs
    :start-after: BEGIN validator blueprint declaration
    :end-before:  END validator blueprint declaration

The ``definitionRef`` function is used to reference a schema definition of a given type. It is 
smart enough to discover the schema definition from the ``referencedType`` list and 
fails to compile if the referenced type is not included.

With all the pieces in place, we can now write the blueprint to a file:

.. literalinclude:: Cip57Blueprint.hs
    :start-after: BEGIN write blueprint to file
    :end-before:  END write blueprint to file

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
we can use the ``SchemaTitle`` and ``SchemaDescription`` annotations:

.. literalinclude:: Cip57Blueprint.hs
    :start-after: BEGIN MyParams annotations
    :end-before:  END MyParams annotations

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

For sum-types its possible to annotate constructors:

.. literalinclude:: Cip57Blueprint.hs
    :start-after: BEGIN MyRedeemer annotations
    :end-before:  END MyRedeemer annotations

to produce the JSON schema definition:

.. code-block:: json

  {
    "oneOf": [
      {
        "$comment": "Left redeemer",
        "dataType": "constructor",
        "fields": [],
        "index": 0
      },
      {
        "$comment": "Right redeemer",
        "dataType": "constructor",
        "fields": [],
        "index": 1
      }
    ]
  }


Result
------

Here is the full `CIP-0057`_ blueprint produced by this "howto" example:

.. code-block:: json

  {
    "$id": "my-contract",
    "$schema": "https://cips.cardano.org/cips/cip57/schemas/plutus-blueprint.json",
    "$vocabulary": {
      "https://cips.cardano.org/cips/cip57": true,
      "https://json-schema.org/draft/2020-12/vocab/applicator": true,
      "https://json-schema.org/draft/2020-12/vocab/core": true,
      "https://json-schema.org/draft/2020-12/vocab/validation": true
    },
    "preamble": {
      "title": "My Contract",
      "description": "A simple contract",
      "version": "1.0.0",
      "plutusVersion": "v2",
      "license": "MIT"
    },
    "validators": [
      {
        "title": "My Validator",
        "description": "An example validator",
        "redeemer": {
          "title": "My Redeemer",
          "description": "A redeemer that does something awesome",
          "purpose": {
            "oneOf": [
              "spend",
              "mint"
            ]
          },
          "schema": {
            "$ref": "#/definitions/MyRedeemer"
          }
        },
        "datum": {
          "title": "My Datum",
          "description": "A datum that contains something awesome",
          "purpose": "spend",
          "schema": {
            "$ref": "#/definitions/Integer"
          }
        },
        "parameters": [
          {
            "title": "My Validator Parameters",
            "description": "Compile-time validator parameters",
            "purpose": "spend",
            "schema": {
              "$ref": "#/definitions/MyParams"
            }
          }
        ]
      }
    ],
    "definitions": {
      "Bool": {
        "dataType": "#boolean"
      },
      "Integer": {
        "dataType": "integer"
      },
      "MyParams": {
        "title": "Title for the MyParams definition",
        "description": "Description for the MyParams definition",
        "dataType": "constructor",
        "fields": [
          {
            "$ref": "#/definitions/Bool"
          },
          {
            "$ref": "#/definitions/Integer"
          }
        ],
        "index": 0
      },
      "MyRedeemer": {
        "oneOf": [
          {
            "$comment": "Left redeemer",
            "dataType": "constructor",
            "fields": [],
            "index": 0
          },
          {
            "$comment": "Right redeemer",
            "dataType": "constructor",
            "fields": [],
            "index": 1
          }
        ]
      }
    }
  }


.. note::
  You can find a more elaborate example of a contract blueprint in the ``Blueprint.Tests``
  module of the plutus repository.

.. _CIP-0057: https://cips.cardano.org/cip/CIP-0057
.. _optional keywords: https://cips.cardano.org/cip/CIP-0057#for-any-data-type

