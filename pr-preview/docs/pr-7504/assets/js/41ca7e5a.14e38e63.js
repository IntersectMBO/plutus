"use strict";
(self["webpackChunkdocusaurus"] = self["webpackChunkdocusaurus"] || []).push([[3736],{

/***/ 2212:
/***/ ((__unused_webpack_module, __webpack_exports__, __webpack_require__) => {

// ESM COMPAT FLAG
__webpack_require__.r(__webpack_exports__);

// EXPORTS
__webpack_require__.d(__webpack_exports__, {
  assets: () => (/* binding */ assets),
  contentTitle: () => (/* binding */ contentTitle),
  "default": () => (/* binding */ MDXContent),
  frontMatter: () => (/* binding */ frontMatter),
  metadata: () => (/* reexport */ site_docs_working_with_scripts_producing_a_blueprint_md_41c_namespaceObject),
  toc: () => (/* binding */ toc)
});

;// ./.docusaurus/docusaurus-plugin-content-docs/default/site-docs-working-with-scripts-producing-a-blueprint-md-41c.json
const site_docs_working_with_scripts_producing_a_blueprint_md_41c_namespaceObject = /*#__PURE__*/JSON.parse('{"id":"working-with-scripts/producing-a-blueprint","title":"Producing a Plutus contract blueprint","description":"Plutus contract blueprints (CIP-0057) are used to document the binary interface of a Plutus contract in a machine-readable format (JSON schema).","source":"@site/docs/working-with-scripts/producing-a-blueprint.md","sourceDirName":"working-with-scripts","slug":"/working-with-scripts/producing-a-blueprint","permalink":"/pr-preview/docs/pr-7504/working-with-scripts/producing-a-blueprint","draft":false,"unlisted":false,"editUrl":"https://github.com/IntersectMBO/plutus/edit/master/doc/docusaurus/docs/working-with-scripts/producing-a-blueprint.md","tags":[],"version":"current","sidebarPosition":3,"frontMatter":{"sidebar_position":3},"sidebar":"tutorialSidebar","previous":{"title":"Script Purposes","permalink":"/pr-preview/docs/pr-7504/working-with-scripts/script-purposes"},"next":{"title":"Optimizing Scripts with asData","permalink":"/pr-preview/docs/pr-7504/working-with-scripts/optimizing-scripts-with-asData"}}');
// EXTERNAL MODULE: ./node_modules/react/jsx-runtime.js
var jsx_runtime = __webpack_require__(4848);
// EXTERNAL MODULE: ./node_modules/@mdx-js/react/lib/index.js
var lib = __webpack_require__(8453);
;// ./docs/working-with-scripts/producing-a-blueprint.md


const frontMatter = {
	sidebar_position: 3
};
const contentTitle = 'Producing a Plutus contract blueprint';

const assets = {

};



const toc = [{
  "value": "Demonstrating the usage of the <code>writeBlueprint</code> function",
  "id": "demonstrating-the-usage-of-the-writeblueprint-function",
  "level": 2
}, {
  "value": "Required pragmas and imports",
  "id": "required-pragmas-and-imports",
  "level": 2
}, {
  "value": "Defining a contract blueprint value",
  "id": "defining-a-contract-blueprint-value",
  "level": 2
}, {
  "value": "Example construction",
  "id": "example-construction",
  "level": 2
}, {
  "value": "Defining a validator blueprint",
  "id": "defining-a-validator-blueprint",
  "level": 2
}, {
  "value": "Writing the blueprint to a file",
  "id": "writing-the-blueprint-to-a-file",
  "level": 2
}, {
  "value": "Annotations",
  "id": "annotations",
  "level": 2
}, {
  "value": "Resulting full blueprint example",
  "id": "resulting-full-blueprint-example",
  "level": 2
}];
function _createMdxContent(props) {
  const _components = {
    a: "a",
    blockquote: "blockquote",
    code: "code",
    em: "em",
    h1: "h1",
    h2: "h2",
    header: "header",
    li: "li",
    p: "p",
    pre: "pre",
    strong: "strong",
    ul: "ul",
    ...(0,lib/* useMDXComponents */.R)(),
    ...props.components
  }, {LiteralInclude} = _components;
  if (!LiteralInclude) _missingMdxReference("LiteralInclude", true);
  return (0,jsx_runtime.jsxs)(jsx_runtime.Fragment, {
    children: [(0,jsx_runtime.jsx)(_components.header, {
      children: (0,jsx_runtime.jsx)(_components.h1, {
        id: "producing-a-plutus-contract-blueprint",
        children: "Producing a Plutus contract blueprint"
      })
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["Plutus contract blueprints (", (0,jsx_runtime.jsx)(_components.a, {
        href: "https://cips.cardano.org/cip/CIP-0057",
        children: "CIP-0057"
      }), ") are used to document the binary interface of a Plutus contract in a machine-readable format (JSON schema)."]
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["A contract blueprint can be produced by using the ", (0,jsx_runtime.jsx)(_components.code, {
        children: "writeBlueprint"
      }), " function exported by the ", (0,jsx_runtime.jsx)(_components.code, {
        children: "PlutusTx.Blueprint"
      }), " module:"]
    }), "\n", (0,jsx_runtime.jsx)(_components.pre, {
      children: (0,jsx_runtime.jsx)(_components.code, {
        className: "language-haskell",
        children: "writeBlueprint\n  :: FilePath\n  -- ^ The file path where the blueprint will be written to,\n  --  e.g. '/tmp/plutus.json'\n  -> ContractBlueprint\n  -- ^ Contains all the necessary information to generate\n  -- a blueprint for a Plutus contract.\n  -> IO ()\n"
      })
    }), "\n", (0,jsx_runtime.jsxs)(_components.h2, {
      id: "demonstrating-the-usage-of-the-writeblueprint-function",
      children: ["Demonstrating the usage of the ", (0,jsx_runtime.jsx)(_components.code, {
        children: "writeBlueprint"
      }), " function"]
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["In order to demonstrate the usage of the ", (0,jsx_runtime.jsx)(_components.code, {
        children: "writeBlueprint"
      }), " function, let's consider the following example validator function and its interface:"]
    }), "\n", (0,jsx_runtime.jsx)(LiteralInclude, {
      file: "Example/Cip57/Blueprint/Main.hs",
      language: "haskell",
      title: "interface types",
      start: "-- BEGIN interface types",
      end: "-- END interface types"
    }), "\n", (0,jsx_runtime.jsx)(LiteralInclude, {
      file: "Example/Cip57/Blueprint/Main.hs",
      language: "haskell",
      title: "validator",
      start: "-- BEGIN validator",
      end: "-- END validator"
    }), "\n", (0,jsx_runtime.jsx)(_components.h2, {
      id: "required-pragmas-and-imports",
      children: "Required pragmas and imports"
    }), "\n", (0,jsx_runtime.jsx)(_components.p, {
      children: "First of all, we need to specify required pragmas and import necessary modules:"
    }), "\n", (0,jsx_runtime.jsx)(LiteralInclude, {
      file: "Example/Cip57/Blueprint/Main.hs",
      language: "haskell",
      title: "pragmas",
      start: "-- BEGIN pragmas",
      end: "-- END pragmas"
    }), "\n", (0,jsx_runtime.jsx)(LiteralInclude, {
      file: "Example/Cip57/Blueprint/Main.hs",
      language: "haskell",
      title: "imports",
      start: "-- BEGIN imports",
      end: "-- END imports"
    }), "\n", (0,jsx_runtime.jsx)(_components.h2, {
      id: "defining-a-contract-blueprint-value",
      children: "Defining a contract blueprint value"
    }), "\n", (0,jsx_runtime.jsx)(_components.p, {
      children: "Next, we define a contract blueprint value of the following type:"
    }), "\n", (0,jsx_runtime.jsx)(_components.pre, {
      children: (0,jsx_runtime.jsx)(_components.code, {
        className: "language-haskell",
        children: "data ContractBlueprint where\n  MkContractBlueprint\n    :: forall referencedTypes\n    . { contractId :: Maybe Text\n        -- ^ An optional identifier for the contract.\n      , contractPreamble :: Preamble\n        -- ^ An object with meta-information about the contract.\n      , contractValidators :: Set (ValidatorBlueprint referencedTypes)\n        -- ^ A set of validator blueprints that are part of the contract.\n      , contractDefinitions :: Definitions referencedTypes\n        -- ^ A registry of schema definitions used across the blueprint.\n      }\n    -> ContractBlueprint\n"
      })
    }), "\n", (0,jsx_runtime.jsxs)(_components.blockquote, {
      children: ["\n", (0,jsx_runtime.jsxs)(_components.p, {
        children: ["📌", " ", (0,jsx_runtime.jsx)(_components.strong, {
          children: "NOTE"
        })]
      }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
        children: ["The ", (0,jsx_runtime.jsx)(_components.code, {
          children: "referencedTypes"
        }), " type parameter is used to track the types used in the contract making sure their schemas are included in the blueprint and that they are referenced in a type-safe way."]
      }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
        children: ["The blueprint will contain JSON schema definitions for all the types used in the contract, including the types ", (0,jsx_runtime.jsx)(_components.strong, {
          children: "nested"
        }), " within the top-level types (", (0,jsx_runtime.jsx)(_components.code, {
          children: "MyParams"
        }), ", ", (0,jsx_runtime.jsx)(_components.code, {
          children: "MyDatum"
        }), ", ", (0,jsx_runtime.jsx)(_components.code, {
          children: "MyRedeemer"
        }), ") recursively."]
      }), "\n"]
    }), "\n", (0,jsx_runtime.jsx)(_components.p, {
      children: "We can construct a value of this type in the following way:"
    }), "\n", (0,jsx_runtime.jsx)(LiteralInclude, {
      file: "Example/Cip57/Blueprint/Main.hs",
      language: "haskell",
      title: "contract blueprint declaration",
      start: "-- BEGIN contract blueprint declaration",
      end: "-- END contract blueprint declaration"
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["The ", (0,jsx_runtime.jsx)(_components.code, {
        children: "contractId"
      }), " field is optional and can be used to give a unique identifier to the contract."]
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["The ", (0,jsx_runtime.jsx)(_components.code, {
        children: "contractPreamble"
      }), " field is a value of type ", (0,jsx_runtime.jsx)(_components.code, {
        children: "PlutusTx.Blueprint.Preamble"
      }), " and contains a meta-information\nabout the contract:"]
    }), "\n", (0,jsx_runtime.jsx)(_components.pre, {
      children: (0,jsx_runtime.jsx)(_components.code, {
        className: "language-haskell",
        children: "data Preamble = MkPreamble\n  { preambleTitle         :: Text\n  -- ^ A short and descriptive title of the contract application\n  , preambleDescription   :: Maybe Text\n  -- ^ A more elaborate description\n  , preambleVersion       :: Text\n  -- ^ A version number for the project.\n  , preamblePlutusVersion :: PlutusVersion\n  -- ^ The Plutus version assumed for all validators\n  , preambleLicense       :: Maybe Text\n  -- ^ A license under which the specification\n  -- and contract code is distributed\n  }\n"
      })
    }), "\n", (0,jsx_runtime.jsx)(_components.h2, {
      id: "example-construction",
      children: "Example construction"
    }), "\n", (0,jsx_runtime.jsx)(_components.p, {
      children: "Here is an example construction:"
    }), "\n", (0,jsx_runtime.jsx)(LiteralInclude, {
      file: "Example/Cip57/Blueprint/Main.hs",
      language: "haskell",
      title: "preamble declaration",
      start: "-- BEGIN preamble declaration",
      end: "-- END preamble declaration"
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["The ", (0,jsx_runtime.jsx)(_components.code, {
        children: "contractDefinitions"
      }), " field is a registry of schema definitions used across the blueprint.\nIt can be constructed using the ", (0,jsx_runtime.jsx)(_components.code, {
        children: "deriveDefinitions"
      }), " function which automatically constructs schema definitions for all the types it is applied to including the types nested within them."]
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["Since every type in the ", (0,jsx_runtime.jsx)(_components.code, {
        children: "referencedTypes"
      }), " list is going to have its derived JSON-schema in the ", (0,jsx_runtime.jsx)(_components.code, {
        children: "contractDefinitions"
      }), " registry under a certain unique ", (0,jsx_runtime.jsx)(_components.code, {
        children: "DefinitionId"
      }), " key, we need to make sure that it has the following instances:"]
    }), "\n", (0,jsx_runtime.jsxs)(_components.ul, {
      children: ["\n", (0,jsx_runtime.jsxs)(_components.li, {
        children: ["\n", (0,jsx_runtime.jsxs)(_components.p, {
          children: [(0,jsx_runtime.jsx)(_components.code, {
            children: "instance HasBlueprintDefinition MyType"
          }), " allows to add a ", (0,jsx_runtime.jsx)(_components.code, {
            children: "MyType"
          }), " schema definition to the ", (0,jsx_runtime.jsx)(_components.code, {
            children: "contractDefinitions"
          }), " registry by providing a ", (0,jsx_runtime.jsx)(_components.code, {
            children: "DefinitionId"
          }), " value for ", (0,jsx_runtime.jsx)(_components.code, {
            children: "MyType"
          }), ", e.g. ", (0,jsx_runtime.jsx)(_components.code, {
            children: "\"my-type\""
          }), "."]
        }), "\n", (0,jsx_runtime.jsx)(_components.p, {
          children: "The good news is that most of the time these instances either already exist (for types defined in the Plutus libraries) or can be derived automatically:"
        }), "\n", (0,jsx_runtime.jsx)(LiteralInclude, {
          file: "Example/Cip57/Blueprint/Main.hs",
          language: "haskell",
          title: "Generically-derived HasBlueprintDefinition instances",
          start: "-- BEGIN derived instances",
          end: "-- END derived instances"
        }), "\n"]
      }), "\n", (0,jsx_runtime.jsxs)(_components.li, {
        children: ["\n", (0,jsx_runtime.jsxs)(_components.p, {
          children: [(0,jsx_runtime.jsx)(_components.code, {
            children: "instance HasBlueprintSchema MyType"
          }), " allows to derive a JSON schema for ", (0,jsx_runtime.jsx)(_components.code, {
            children: "MyType"
          }), "."]
        }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
          children: ["Types that are covered by a blueprint are exposed via the validator arguments and therefore must be convertible to/from ", (0,jsx_runtime.jsx)(_components.code, {
            children: "Data"
          }), " representation. The conversion is done using instances of ", (0,jsx_runtime.jsx)(_components.code, {
            children: "ToData"
          }), ", ", (0,jsx_runtime.jsx)(_components.code, {
            children: "FromData"
          }), " and optionally ", (0,jsx_runtime.jsx)(_components.code, {
            children: "UnsafeFromData"
          }), "."]
        }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
          children: ["You probably already have these instances derived with Template Haskell functions ", (0,jsx_runtime.jsx)(_components.code, {
            children: "makeIsDataIndexed"
          }), " or ", (0,jsx_runtime.jsx)(_components.code, {
            children: "unstableMakeIsData"
          }), " which are located in the ", (0,jsx_runtime.jsx)(_components.code, {
            children: "PlutusTx.IsData.TH"
          }), " module. You can add derivation of the\n", (0,jsx_runtime.jsx)(_components.code, {
            children: "HasBlueprintSchema"
          }), " instance very easily:"]
        }), "\n", (0,jsx_runtime.jsxs)(_components.ul, {
          children: ["\n", (0,jsx_runtime.jsxs)(_components.li, {
            children: ["Replace usages of ", (0,jsx_runtime.jsx)(_components.code, {
              children: "PlutusTx.IsData.TH.makeIsDataIndexed"
            }), " with ", (0,jsx_runtime.jsx)(_components.code, {
              children: "PlutusTx.Blueprint.TH.makeIsDataSchemaIndexed"
            }), "."]
          }), "\n", (0,jsx_runtime.jsxs)(_components.li, {
            children: ["Replace usages of ", (0,jsx_runtime.jsx)(_components.code, {
              children: "PlutusTx.IsData.TH.unstableMakeIsData"
            }), " with ", (0,jsx_runtime.jsx)(_components.code, {
              children: "PlutusTx.Blueprint.TH.unstableMakeIsDataSchema"
            }), "."]
          }), "\n"]
        }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
          children: ["(This way ", (0,jsx_runtime.jsx)(_components.code, {
            children: "HasBlueprintSchema"
          }), " instance is guaranteed to correspond to the ", (0,jsx_runtime.jsx)(_components.code, {
            children: "ToData"
          }), " and ", (0,jsx_runtime.jsx)(_components.code, {
            children: "FromData"
          }), " instances which are derived with it.)"]
        }), "\n", (0,jsx_runtime.jsx)(_components.p, {
          children: "Here is an example:"
        }), "\n", (0,jsx_runtime.jsx)(LiteralInclude, {
          file: "Example/Cip57/Blueprint/Main.hs",
          language: "haskell",
          title: "TH-derived HasBlueprintSchema instances",
          start: "-- BEGIN makeIsDataSchemaIndexed",
          end: "-- END makeIsDataSchemaIndexed"
        }), "\n"]
      }), "\n"]
    }), "\n", (0,jsx_runtime.jsx)(_components.h2, {
      id: "defining-a-validator-blueprint",
      children: "Defining a validator blueprint"
    }), "\n", (0,jsx_runtime.jsx)(_components.p, {
      children: "Finally, we need to define a validator blueprint for each validator used in the contract."
    }), "\n", (0,jsx_runtime.jsx)(_components.p, {
      children: "Our contract can contain one or more validators. For each one we need to provide a description as a value of the following type:"
    }), "\n", (0,jsx_runtime.jsxs)(_components.blockquote, {
      children: ["\n", (0,jsx_runtime.jsx)(_components.pre, {
        children: (0,jsx_runtime.jsx)(_components.code, {
          className: "language-haskell",
          children: "data ValidatorBlueprint (referencedTypes :: [Type]) = MkValidatorBlueprint\n  { validatorTitle       :: Text\n  -- ^ A short and descriptive name for the validator.\n  , validatorDescription :: Maybe Text\n  -- ^ An informative description of the validator.\n  , validatorRedeemer    :: ArgumentBlueprint referencedTypes\n  -- ^ A description of the redeemer format expected by this validator.\n  , validatorDatum       :: Maybe (ArgumentBlueprint referencedTypes)\n  -- ^ A description of the datum format expected by this validator.\n  , validatorParameters  :: [ParameterBlueprint referencedTypes]\n  -- ^ A list of parameters required by the script.\n  , validatorCompiled    :: Maybe CompiledValidator\n  -- ^ A full compiled and CBOR-encoded serialized flat script together with its hash.\n  }\n  deriving stock (Show, Eq, Ord)\n"
        })
      }), "\n"]
    }), "\n", (0,jsx_runtime.jsx)(_components.p, {
      children: "In our example, this would be:"
    }), "\n", (0,jsx_runtime.jsx)(LiteralInclude, {
      file: "Example/Cip57/Blueprint/Main.hs",
      language: "haskell",
      title: "validator blueprint declaration",
      start: "-- BEGIN validator blueprint declaration",
      end: "-- END validator blueprint declaration"
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["The ", (0,jsx_runtime.jsx)(_components.code, {
        children: "definitionRef"
      }), " function is used to reference a schema definition of a given type.\nIt is smart enough to discover the schema definition from the ", (0,jsx_runtime.jsx)(_components.code, {
        children: "referencedType"
      }), " list and fails to compile if the referenced type is not included."]
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["If you want to provide validator code with its hash, you can use the ", (0,jsx_runtime.jsx)(_components.code, {
        children: "compiledValidator"
      }), " function:"]
    }), "\n", (0,jsx_runtime.jsx)(_components.pre, {
      children: (0,jsx_runtime.jsx)(_components.code, {
        className: "language-haskell",
        children: "compiledValidator\n  :: PlutusVersion\n  -- ^ Plutus version (e.g. `PlutusV3`) to calculate the hash of the validator code.\n  -> ByteString\n  -- ^ The compiled validator code.\n  -> CompiledValidator\n"
      })
    }), "\n", (0,jsx_runtime.jsx)(_components.h2, {
      id: "writing-the-blueprint-to-a-file",
      children: "Writing the blueprint to a file"
    }), "\n", (0,jsx_runtime.jsx)(_components.p, {
      children: "With all the pieces in place, we can now write the blueprint to a file:"
    }), "\n", (0,jsx_runtime.jsx)(LiteralInclude, {
      file: "Example/Cip57/Blueprint/Main.hs",
      language: "haskell",
      title: "write blueprint to file",
      start: "-- BEGIN write blueprint to file",
      end: "-- END write blueprint to file"
    }), "\n", (0,jsx_runtime.jsx)(_components.h2, {
      id: "annotations",
      children: "Annotations"
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["Any ", (0,jsx_runtime.jsx)(_components.a, {
        href: "https://cips.cardano.org/cip/CIP-0057",
        children: "CIP-0057"
      }), " blueprint type definition may include ", (0,jsx_runtime.jsx)(_components.a, {
        href: "https://cips.cardano.org/cip/CIP-0057#for-any-data-type",
        children: "optional keywords"
      }), " to provide additional information:"]
    }), "\n", (0,jsx_runtime.jsxs)(_components.ul, {
      children: ["\n", (0,jsx_runtime.jsx)(_components.li, {
        children: "title"
      }), "\n", (0,jsx_runtime.jsx)(_components.li, {
        children: "description"
      }), "\n", (0,jsx_runtime.jsx)(_components.li, {
        children: "$comment"
      }), "\n"]
    }), "\n", (0,jsx_runtime.jsx)(_components.p, {
      children: "It's possible to add these keywords to a Blueprint type definition by annotating the Haskell type from which it's derived with a corresponding annotation:"
    }), "\n", (0,jsx_runtime.jsxs)(_components.ul, {
      children: ["\n", (0,jsx_runtime.jsx)(_components.li, {
        children: (0,jsx_runtime.jsx)(_components.code, {
          children: "SchemaTitle"
        })
      }), "\n", (0,jsx_runtime.jsx)(_components.li, {
        children: (0,jsx_runtime.jsx)(_components.code, {
          children: "SchemaDescription"
        })
      }), "\n", (0,jsx_runtime.jsx)(_components.li, {
        children: (0,jsx_runtime.jsx)(_components.code, {
          children: "SchemaComment"
        })
      }), "\n"]
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["For example, to add a title and description to the ", (0,jsx_runtime.jsx)(_components.code, {
        children: "MyParams"
      }), " type, we can use the ", (0,jsx_runtime.jsx)(_components.code, {
        children: "SchemaTitle"
      }), " and ", (0,jsx_runtime.jsx)(_components.code, {
        children: "SchemaDescription"
      }), " annotations:"]
    }), "\n", (0,jsx_runtime.jsx)(LiteralInclude, {
      file: "Example/Cip57/Blueprint/Main.hs",
      language: "haskell",
      title: "MyParams annotations",
      start: "-- BEGIN MyParams annotations",
      end: "-- END MyParams annotations"
    }), "\n", (0,jsx_runtime.jsx)(_components.p, {
      children: "These annotations result in the following JSON schema definition:"
    }), "\n", (0,jsx_runtime.jsx)(_components.pre, {
      children: (0,jsx_runtime.jsx)(_components.code, {
        className: "language-json",
        children: "{\n  \"title\": \"Title for the MyParams definition\",\n  \"description\": \"Description for the MyParams definition\",\n  \"dataType\": \"constructor\",\n  \"fields\": [\n    { \"$ref\": \"#/definitions/Bool\" },\n    { \"$ref\": \"#/definitions/Integer\" }\n  ],\n  \"index\": 0\n}\n"
      })
    }), "\n", (0,jsx_runtime.jsx)(_components.p, {
      children: "For sum-types, it's possible to annotate constructors:"
    }), "\n", (0,jsx_runtime.jsx)(LiteralInclude, {
      file: "Example/Cip57/Blueprint/Main.hs",
      language: "haskell",
      title: "MyRedeemer annotations",
      start: "-- BEGIN MyRedeemer annotations",
      end: "-- END MyRedeemer annotations"
    }), "\n", (0,jsx_runtime.jsx)(_components.p, {
      children: "These annotations result in the following JSON schema definition:"
    }), "\n", (0,jsx_runtime.jsx)(_components.pre, {
      children: (0,jsx_runtime.jsx)(_components.code, {
        className: "language-json",
        children: "{\n  \"oneOf\": [\n    {\n      \"$comment\": \"Left redeemer\",\n      \"dataType\": \"constructor\",\n      \"fields\": [],\n      \"index\": 0\n    },\n    {\n      \"$comment\": \"Right redeemer\",\n      \"dataType\": \"constructor\",\n      \"fields\": [],\n      \"index\": 1\n    }\n  ]\n}\n"
      })
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["It is also possible to annotate a validator's parameter or argument ", (0,jsx_runtime.jsx)(_components.strong, {
        children: "type"
      }), " (as opposed to annotating ", (0,jsx_runtime.jsx)(_components.em, {
        children: "constructors"
      }), "):"]
    }), "\n", (0,jsx_runtime.jsx)(_components.pre, {
      children: (0,jsx_runtime.jsx)(_components.code, {
        className: "language-haskell",
        children: "{-# ANN type MyParams (SchemaTitle \"Example parameter title\") #-}\n{-# ANN type MyRedeemer (SchemaTitle \"Example redeemer title\") #-}\n"
      })
    }), "\n", (0,jsx_runtime.jsx)(_components.p, {
      children: "Then, instead of providing them literally:"
    }), "\n", (0,jsx_runtime.jsx)(_components.pre, {
      children: (0,jsx_runtime.jsx)(_components.code, {
        className: "language-haskell",
        children: "myValidator =\n  MkValidatorBlueprint\n    { ... elided\n    , validatorParameters =\n        [ MkParameterBlueprint\n            { parameterTitle = Just \"My Validator Parameters\"\n            , parameterDescription = Just \"Compile-time validator parameters\"\n            , parameterPurpose = Set.singleton Spend\n            , parameterSchema = definitionRef @MyParams\n            }\n        ]\n    , validatorRedeemer =\n        MkArgumentBlueprint\n          { argumentTitle = Just \"My Redeemer\"\n          , argumentDescription = Just \"A redeemer that does something awesome\"\n          , argumentPurpose = Set.fromList [Spend, Mint]\n          , argumentSchema = definitionRef @MyRedeemer\n          }\n    , ... elided\n    }\n"
      })
    }), "\n", (0,jsx_runtime.jsx)(_components.p, {
      children: "Use TH to have a more concise version:"
    }), "\n", (0,jsx_runtime.jsx)(_components.pre, {
      children: (0,jsx_runtime.jsx)(_components.code, {
        className: "language-haskell",
        children: "myValidator =\n  MkValidatorBlueprint\n    { ... elided\n    , validatorParameters =\n        [ $(deriveParameterBlueprint ''MyParams (Set.singleton Purpose.Spend)) ]\n    , validatorRedeemer =\n        $(deriveArgumentBlueprint ''MyRedeemer (Set.fromList [Purpose.Spend, Purpose.Mint]))\n    , ... elided\n    }\n"
      })
    }), "\n", (0,jsx_runtime.jsx)(_components.h2, {
      id: "resulting-full-blueprint-example",
      children: "Resulting full blueprint example"
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["Here is the full ", (0,jsx_runtime.jsx)(_components.a, {
        href: "https://cips.cardano.org/cip/CIP-0057",
        children: "CIP-0057"
      }), " blueprint produced by this example: ", (0,jsx_runtime.jsx)(_components.a, {
        target: "_blank",
        "data-noBrokenLinkCheck": true,
        href: (__webpack_require__(4759)/* ["default"] */ .A) + "",
        children: "plutus.json"
      })]
    }), "\n", (0,jsx_runtime.jsxs)(_components.blockquote, {
      children: ["\n", (0,jsx_runtime.jsxs)(_components.p, {
        children: ["📌", " ", (0,jsx_runtime.jsx)(_components.strong, {
          children: "NOTE"
        })]
      }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
        children: ["You can find a more elaborate example of a contract blueprint in the ", (0,jsx_runtime.jsx)(_components.code, {
          children: "Blueprint.Tests"
        }), " module of the Plutus repository."]
      }), "\n"]
    })]
  });
}
function MDXContent(props = {}) {
  const {wrapper: MDXLayout} = {
    ...(0,lib/* useMDXComponents */.R)(),
    ...props.components
  };
  return MDXLayout ? (0,jsx_runtime.jsx)(MDXLayout, {
    ...props,
    children: (0,jsx_runtime.jsx)(_createMdxContent, {
      ...props
    })
  }) : _createMdxContent(props);
}
function _missingMdxReference(id, component) {
  throw new Error("Expected " + (component ? "component" : "object") + " `" + id + "` to be defined: you likely forgot to import, pass, or provide it.");
}



/***/ }),

/***/ 4759:
/***/ ((__unused_webpack_module, __webpack_exports__, __webpack_require__) => {

/* harmony export */ __webpack_require__.d(__webpack_exports__, {
/* harmony export */   A: () => (__WEBPACK_DEFAULT_EXPORT__)
/* harmony export */ });
/* harmony default export */ const __WEBPACK_DEFAULT_EXPORT__ = (__webpack_require__.p + "assets/files/plutus-3dc4d6c5cd06e06cdfaef8de8bbdd010.json");

/***/ }),

/***/ 8453:
/***/ ((__unused_webpack___webpack_module__, __webpack_exports__, __webpack_require__) => {

/* harmony export */ __webpack_require__.d(__webpack_exports__, {
/* harmony export */   R: () => (/* binding */ useMDXComponents),
/* harmony export */   x: () => (/* binding */ MDXProvider)
/* harmony export */ });
/* harmony import */ var react__WEBPACK_IMPORTED_MODULE_0__ = __webpack_require__(6540);
/**
 * @import {MDXComponents} from 'mdx/types.js'
 * @import {Component, ReactElement, ReactNode} from 'react'
 */

/**
 * @callback MergeComponents
 *   Custom merge function.
 * @param {Readonly<MDXComponents>} currentComponents
 *   Current components from the context.
 * @returns {MDXComponents}
 *   Additional components.
 *
 * @typedef Props
 *   Configuration for `MDXProvider`.
 * @property {ReactNode | null | undefined} [children]
 *   Children (optional).
 * @property {Readonly<MDXComponents> | MergeComponents | null | undefined} [components]
 *   Additional components to use or a function that creates them (optional).
 * @property {boolean | null | undefined} [disableParentContext=false]
 *   Turn off outer component context (default: `false`).
 */



/** @type {Readonly<MDXComponents>} */
const emptyComponents = {}

const MDXContext = react__WEBPACK_IMPORTED_MODULE_0__.createContext(emptyComponents)

/**
 * Get current components from the MDX Context.
 *
 * @param {Readonly<MDXComponents> | MergeComponents | null | undefined} [components]
 *   Additional components to use or a function that creates them (optional).
 * @returns {MDXComponents}
 *   Current components.
 */
function useMDXComponents(components) {
  const contextComponents = react__WEBPACK_IMPORTED_MODULE_0__.useContext(MDXContext)

  // Memoize to avoid unnecessary top-level context changes
  return react__WEBPACK_IMPORTED_MODULE_0__.useMemo(
    function () {
      // Custom merge via a function prop
      if (typeof components === 'function') {
        return components(contextComponents)
      }

      return {...contextComponents, ...components}
    },
    [contextComponents, components]
  )
}

/**
 * Provider for MDX context.
 *
 * @param {Readonly<Props>} properties
 *   Properties.
 * @returns {ReactElement}
 *   Element.
 * @satisfies {Component}
 */
function MDXProvider(properties) {
  /** @type {Readonly<MDXComponents>} */
  let allComponents

  if (properties.disableParentContext) {
    allComponents =
      typeof properties.components === 'function'
        ? properties.components(emptyComponents)
        : properties.components || emptyComponents
  } else {
    allComponents = useMDXComponents(properties.components)
  }

  return react__WEBPACK_IMPORTED_MODULE_0__.createElement(
    MDXContext.Provider,
    {value: allComponents},
    properties.children
  )
}


/***/ })

}]);