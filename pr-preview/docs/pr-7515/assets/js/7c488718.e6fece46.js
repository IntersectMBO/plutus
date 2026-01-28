"use strict";
(self["webpackChunkdocusaurus"] = self["webpackChunkdocusaurus"] || []).push([[9073],{

/***/ 765:
/***/ ((__unused_webpack_module, __webpack_exports__, __webpack_require__) => {

// ESM COMPAT FLAG
__webpack_require__.r(__webpack_exports__);

// EXPORTS
__webpack_require__.d(__webpack_exports__, {
  assets: () => (/* binding */ assets),
  contentTitle: () => (/* binding */ contentTitle),
  "default": () => (/* binding */ MDXContent),
  frontMatter: () => (/* binding */ frontMatter),
  metadata: () => (/* reexport */ site_docs_working_with_scripts_ledger_language_version_md_7c4_namespaceObject),
  toc: () => (/* binding */ toc)
});

;// ./.docusaurus/docusaurus-plugin-content-docs/default/site-docs-working-with-scripts-ledger-language-version-md-7c4.json
const site_docs_working_with_scripts_ledger_language_version_md_7c4_namespaceObject = /*#__PURE__*/JSON.parse('{"id":"working-with-scripts/ledger-language-version","title":"Plutus Ledger Language Version (Plutus V1/V2/V3)","description":"As explained in Different Notions of Version, Plutus V1, V2 and V3 are not distinct programming languages; the primary difference lies in the arguments the script receives from the ledger, and the value it returns.","source":"@site/docs/working-with-scripts/ledger-language-version.md","sourceDirName":"working-with-scripts","slug":"/working-with-scripts/ledger-language-version","permalink":"/pr-preview/docs/pr-7515/working-with-scripts/ledger-language-version","draft":false,"unlisted":false,"editUrl":"https://github.com/IntersectMBO/plutus/edit/master/doc/docusaurus/docs/working-with-scripts/ledger-language-version.md","tags":[],"version":"current","sidebarPosition":1,"frontMatter":{"sidebar_position":1},"sidebar":"tutorialSidebar","previous":{"title":"Working with scripts","permalink":"/pr-preview/docs/pr-7515/category/working-with-scripts"},"next":{"title":"Script Purposes","permalink":"/pr-preview/docs/pr-7515/working-with-scripts/script-purposes"}}');
// EXTERNAL MODULE: ./node_modules/react/jsx-runtime.js
var jsx_runtime = __webpack_require__(4848);
// EXTERNAL MODULE: ./node_modules/@mdx-js/react/lib/index.js
var lib = __webpack_require__(8453);
;// ./docs/working-with-scripts/ledger-language-version.md


const frontMatter = {
	sidebar_position: 1
};
const contentTitle = 'Plutus Ledger Language Version (Plutus V1/V2/V3)';

const assets = {

};



const toc = [{
  "value": "ScriptContext",
  "id": "scriptcontext",
  "level": 2
}, {
  "value": "Plutus V1",
  "id": "plutus-v1",
  "level": 2
}, {
  "value": "Spending Scripts",
  "id": "spending-scripts",
  "level": 3
}, {
  "value": "Minting, Certifying and Rewarding Scripts",
  "id": "minting-certifying-and-rewarding-scripts",
  "level": 3
}, {
  "value": "Script Evaluation and Unsaturated Scripts",
  "id": "script-evaluation-and-unsaturated-scripts",
  "level": 3
}, {
  "value": "Plutus V2",
  "id": "plutus-v2",
  "level": 2
}, {
  "value": "Plutus V3",
  "id": "plutus-v3",
  "level": 2
}];
function _createMdxContent(props) {
  const _components = {
    a: "a",
    code: "code",
    h1: "h1",
    h2: "h2",
    h3: "h3",
    header: "header",
    hr: "hr",
    li: "li",
    ol: "ol",
    p: "p",
    pre: "pre",
    section: "section",
    sup: "sup",
    ul: "ul",
    ...(0,lib/* useMDXComponents */.R)(),
    ...props.components
  };
  return (0,jsx_runtime.jsxs)(jsx_runtime.Fragment, {
    children: [(0,jsx_runtime.jsx)(_components.header, {
      children: (0,jsx_runtime.jsx)(_components.h1, {
        id: "plutus-ledger-language-version-plutus-v1v2v3",
        children: "Plutus Ledger Language Version (Plutus V1/V2/V3)"
      })
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["As explained in ", (0,jsx_runtime.jsx)(_components.a, {
        href: "/pr-preview/docs/pr-7515/essential-concepts/versions",
        children: "Different Notions of Version"
      }), ", Plutus V1, V2 and V3 are not distinct programming languages; the primary difference lies in the arguments the script receives from the ledger, and the value it returns.\nTherefore, Plutus V1, V2 and V3 can be understood as type signatures, in the sense that they each represent a subset of Untyped Plutus Core (UPLC) programs with specific types.\nAny UPLC program that matches the expected argument and return types can be considered and used as a Plutus V1, V2 or V3 script."]
    }), "\n", (0,jsx_runtime.jsx)(_components.p, {
      children: "Next we'll start with a brief overview of the script context, followed by an in-depth explanation of these type signatures."
    }), "\n", (0,jsx_runtime.jsx)(_components.h2, {
      id: "scriptcontext",
      children: "ScriptContext"
    }), "\n", (0,jsx_runtime.jsx)(_components.p, {
      children: "Every Plutus script receives an argument called script context.\nIt contains information about the transaction the script is validating, such as inputs, outputs, transaction fee, signatures and so on.\nAdditionally, since a transaction may have multiple things to validate (e.g., it may be spending multiple script UTXOs, or performing both spending and minting), each of which is validated by a separate script, the script context also has a script purpose field, telling the script what exactly it is supposed to validate."
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["Plutus V1, V2 and V3 scripts receive different script contexts even when all else is equal.\nThis is because different ledger language versions are introduced in different ledger eras; transactions in different ledger eras have different fields - a new era usually adds new fields and may also change existing fields.\nAs a result, The script contexts for Plutus V1, V2 and V3 also have different fields, leading to different Haskell types (", (0,jsx_runtime.jsx)(_components.a, {
        href: "https://plutus.cardano.intersectmbo.org/haddock/master/plutus-ledger-api/PlutusLedgerApi-V1-Contexts.html#t:ScriptContext",
        children: "V1"
      }), ", ", (0,jsx_runtime.jsx)(_components.a, {
        href: "https://plutus.cardano.intersectmbo.org/haddock/master/plutus-ledger-api/PlutusLedgerApi-V2-Contexts.html#t:ScriptContext",
        children: "V2"
      }), ", ", (0,jsx_runtime.jsx)(_components.a, {
        href: "https://plutus.cardano.intersectmbo.org/haddock/master/plutus-ledger-api/PlutusLedgerApi-V3-Contexts.html#t:ScriptContext",
        children: "V3"
      }), ").\nWe cannot modify the script context fields of an existing ledger language version once it is published, since it would break existing scripts."]
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["In general, a ledger language version cannot be used in a transaction, if the ledger language version was introduced in ledger era A, the transaction uses features in ledger era B, and A is earlier than B.\nFor instance, Plutus V1 (introduced in the Alonzo era) scripts cannot be used in a transaction which utilizes inline datums (a Babbage era feature); Plutus V2 (introduced in the Babbage era) scripts cannot be used in a transaction that registers a DRep (introduced in the Conway era)", (0,jsx_runtime.jsx)(_components.sup, {
        children: (0,jsx_runtime.jsx)(_components.a, {
          href: "#user-content-fn-1",
          id: "user-content-fnref-1",
          "data-footnote-ref": true,
          "aria-describedby": "footnote-label",
          children: "1"
        })
      }), "."]
    }), "\n", (0,jsx_runtime.jsx)(_components.h2, {
      id: "plutus-v1",
      children: "Plutus V1"
    }), "\n", (0,jsx_runtime.jsx)(_components.p, {
      children: "Plutus V1 is the initial ledger language version, enabled at the Alonzo hard fork, a hard fork that introduced the Alonzo era."
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["Plutus V1 scripts have four ", (0,jsx_runtime.jsx)(_components.a, {
        href: "https://plutus.cardano.intersectmbo.org/haddock/master/plutus-ledger-api/PlutusLedgerApi-V1-Contexts.html#t:ScriptPurpose",
        children: "script purposes"
      }), ": spending, minting, certifying, and rewarding", (0,jsx_runtime.jsx)(_components.sup, {
        children: (0,jsx_runtime.jsx)(_components.a, {
          href: "#user-content-fn-2",
          id: "user-content-fnref-2",
          "data-footnote-ref": true,
          "aria-describedby": "footnote-label",
          children: "2"
        })
      }), ".\nThe arguments a Plutus V1 script receives depend on the script purpose.\nThere is no requirement on the return value of a Plutus V1 script: script evaluation succeeds as long as the evaluation terminates without error, and the execution budget is not exceeded."]
    }), "\n", (0,jsx_runtime.jsx)(_components.h3, {
      id: "spending-scripts",
      children: "Spending Scripts"
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["A Plutus V1 spending script receives three arguments corresponding to datum, redeemer and script context.\nAll arguments are encoded as ", (0,jsx_runtime.jsx)(_components.code, {
        children: "BuiltinData"
      }), ".\nThus in Plinth, a spending script has the following type:"]
    }), "\n", (0,jsx_runtime.jsx)(_components.pre, {
      children: (0,jsx_runtime.jsx)(_components.code, {
        className: "language-haskell",
        children: "BuiltinData -> BuiltinData -> BuiltinData -> any\n"
      })
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["To create a Plutus script using Plinth, it is common to first write a function that takes the corresponding Haskell domain types and returns ", (0,jsx_runtime.jsx)(_components.code, {
        children: "Bool"
      }), ".\nFor example, the following function can be used to implement the main business logic of a Plutus V1 spending script:"]
    }), "\n", (0,jsx_runtime.jsx)(_components.pre, {
      children: (0,jsx_runtime.jsx)(_components.code, {
        className: "language-haskell",
        children: "myV1SpendingScriptTyped :: MyDatum -> MyRedeemer -> PlutusLedgerApi.V1.ScriptContext -> Bool\n"
      })
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["where ", (0,jsx_runtime.jsx)(_components.code, {
        children: "MyDatum"
      }), " and ", (0,jsx_runtime.jsx)(_components.code, {
        children: "MyRedeemer"
      }), " are your user-defined Haskell types specific to your contract."]
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["From ", (0,jsx_runtime.jsx)(_components.code, {
        children: "myV1SpendingScriptTyped"
      }), ", you can obtain ", (0,jsx_runtime.jsx)(_components.code, {
        children: "BuiltinData -> BuiltinData -> BuiltinData -> any"
      }), ", and subsequently compile it to UPLC, via"]
    }), "\n", (0,jsx_runtime.jsx)(_components.pre, {
      children: (0,jsx_runtime.jsx)(_components.code, {
        className: "language-haskell",
        children: "myV1SpendingScriptUntyped :: BuiltinData -> BuiltinData -> BuiltinData -> BuiltinUnit\nmyV1SpendingScriptUntyped myDatum myRedeemer scriptContext =\n  PlutusTx.Prelude.check\n    ( myV1SpendingScriptTyped\n        (PlutusTx.unsafeFromBuiltinData myDatum)\n        (PlutusTx.unsafeFromBuiltinData myRedeemer)\n        (PlutusTx.unsafeFromBuiltinData scriptContext)\n    )\n\nmyV1SpendingScriptCompiled :: CompiledCode (BuiltinData -> BuiltinData -> BuiltinData -> BuiltinUnit)\nmyV1SpendingScriptCompiled = $$(PlutusTx.compile [||myV1SpendingScriptUntyped||])\n"
      })
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: [(0,jsx_runtime.jsx)(_components.code, {
        children: "unsafeFromBuiltinData"
      }), " is a method from the ", (0,jsx_runtime.jsx)(_components.a, {
        href: "https://plutus.cardano.intersectmbo.org/haddock/master/plutus-ledger-api/PlutusLedgerApi-V1.html#t:UnsafeFromData",
        children: (0,jsx_runtime.jsx)(_components.code, {
          children: "UnsafeFromData"
        })
      }), " class.\nEach call to ", (0,jsx_runtime.jsx)(_components.code, {
        children: "unsafeFromBuiltinData"
      }), " decodes a ", (0,jsx_runtime.jsx)(_components.code, {
        children: "BuiltinData"
      }), " into a value of a Haskell domain type, failing if the conversion fails.\nThe ", (0,jsx_runtime.jsx)(_components.code, {
        children: "check"
      }), " function takes a ", (0,jsx_runtime.jsx)(_components.code, {
        children: "Bool"
      }), " and returns a ", (0,jsx_runtime.jsx)(_components.code, {
        children: "BuiltinUnit"
      }), ", throwing an error if the input is ", (0,jsx_runtime.jsx)(_components.code, {
        children: "False"
      }), ".\nIt is needed because returning ", (0,jsx_runtime.jsx)(_components.code, {
        children: "False"
      }), " does not cause the validation to fail; to fail the validation, an error needs to be thrown."]
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["In this example the script happens to return ", (0,jsx_runtime.jsx)(_components.code, {
        children: "BuiltinUnit"
      }), ", but this is not a requirement for Plutus V1."]
    }), "\n", (0,jsx_runtime.jsx)(_components.h3, {
      id: "minting-certifying-and-rewarding-scripts",
      children: "Minting, Certifying and Rewarding Scripts"
    }), "\n", (0,jsx_runtime.jsx)(_components.p, {
      children: "Unlike spending scripts, Plutus V1 scripts for minting, certifying and rewarding purposes take one fewer argument: there is no datum argument.\nThus in Plinth, a minting, certifying or rewarding script should have the following type:"
    }), "\n", (0,jsx_runtime.jsx)(_components.pre, {
      children: (0,jsx_runtime.jsx)(_components.code, {
        className: "language-haskell",
        children: "BuiltinData -> BuiltinData -> any\n"
      })
    }), "\n", (0,jsx_runtime.jsx)(_components.p, {
      children: "Since this type signature is shared by minting, certifying and rewarding scripts, the same script can be used for multiple of these three purposes, for example"
    }), "\n", (0,jsx_runtime.jsx)(_components.pre, {
      children: (0,jsx_runtime.jsx)(_components.code, {
        className: "language-haskell",
        children: "myV1MintingAndRewardingScriptTyped :: MyRedeemer -> PlutusLedgerApi.V1.ScriptContext -> Bool\nmyV1MintingAndRewardingScriptTyped myRedeemer scriptContext =\n  case scriptContextPurpose scriptContext of\n    Minting cs -> -- Perform minting validation\n    Rewarding cred -> -- Perform rewarding validation\n"
      })
    }), "\n", (0,jsx_runtime.jsx)(_components.p, {
      children: "Because spending scripts take one more argument, the same script cannot be used both for spending validation and for a different purpose (minting, certifying or rewarding)."
    }), "\n", (0,jsx_runtime.jsx)(_components.h3, {
      id: "script-evaluation-and-unsaturated-scripts",
      children: "Script Evaluation and Unsaturated Scripts"
    }), "\n", (0,jsx_runtime.jsx)(_components.p, {
      children: "As said before, evaluating a Plutus V1 and V2 script succeeds as long as the evaluation terminates without error, and the budget is not exceeded."
    }), "\n", (0,jsx_runtime.jsx)(_components.p, {
      children: "This means, crucially, that an unsaturated script (a script expecting more arguments than it receives) succeeds trivially, since the evaluation terminates almost immediately and returns a lambda.\nThus be careful: if, for example, you accidentally use a spending script (which expects three arguments) as a minting script (which will receive two arguments), it will always succeed, which is obviously not what you want."
    }), "\n", (0,jsx_runtime.jsx)(_components.h2, {
      id: "plutus-v2",
      children: "Plutus V2"
    }), "\n", (0,jsx_runtime.jsx)(_components.p, {
      children: "Plutus V2 was enabled at the Vasil hard fork, which introduced the Babbage era."
    }), "\n", (0,jsx_runtime.jsx)(_components.p, {
      children: "Plutus V2 shares several similarities with Plutus V1:"
    }), "\n", (0,jsx_runtime.jsxs)(_components.ul, {
      children: ["\n", (0,jsx_runtime.jsx)(_components.li, {
        children: "It supports the same four script purposes."
      }), "\n", (0,jsx_runtime.jsx)(_components.li, {
        children: "The number of arguments a Plutus V2 script receives is identical to Plutus V1: three for spending scripts, and two for other script purposes."
      }), "\n", (0,jsx_runtime.jsx)(_components.li, {
        children: "Script evaluation succeeds as long as no errors occur and the budget is not exceeded."
      }), "\n"]
    }), "\n", (0,jsx_runtime.jsx)(_components.p, {
      children: "The differences between Plutus V1 and Plutus V2 include:"
    }), "\n", (0,jsx_runtime.jsxs)(_components.ul, {
      children: ["\n", (0,jsx_runtime.jsxs)(_components.li, {
        children: ["Plutus V2 can be used in transactions that utilizes Babbage era features like ", (0,jsx_runtime.jsx)(_components.a, {
          href: "https://cips.cardano.org/cip/CIP-0032",
          children: "inline datums"
        }), " and ", (0,jsx_runtime.jsx)(_components.a, {
          href: "https://cips.cardano.org/cip/CIP-0040",
          children: "collateral output"
        }), ", while Plutus V1 cannot (except for reference scripts, as noted earlier)."]
      }), "\n", (0,jsx_runtime.jsxs)(_components.li, {
        children: ["Plutus V2's script context contains more fields than Plutus V1 due to new transaction features.\nWhen writing a Plutus V2 script, you should use the ", (0,jsx_runtime.jsx)(_components.code, {
          children: "ScriptContext"
        }), " data type from ", (0,jsx_runtime.jsx)(_components.code, {
          children: "PlutusLedgerApi.V2"
        }), "."]
      }), "\n", (0,jsx_runtime.jsxs)(_components.li, {
        children: ["For now, Plutus V2 supports more builtin functions than Plutus V1, including ", (0,jsx_runtime.jsx)(_components.code, {
          children: "serialiseData"
        }), ", ", (0,jsx_runtime.jsx)(_components.code, {
          children: "verifyEcdsaSecp256k1Signature"
        }), " and ", (0,jsx_runtime.jsx)(_components.code, {
          children: "verifySchnorrSecp256k1Signature"
        }), ".\nHowever, as explained in ", (0,jsx_runtime.jsx)(_components.a, {
          href: "/pr-preview/docs/pr-7515/essential-concepts/versions",
          children: "Different Notions of Version"
        }), ", we plan to enable all builtin functions across all ledger language versions in the future."]
      }), "\n"]
    }), "\n", (0,jsx_runtime.jsx)(_components.h2, {
      id: "plutus-v3",
      children: "Plutus V3"
    }), "\n", (0,jsx_runtime.jsx)(_components.p, {
      children: "Plutus V3 was enabled at the Chang hard fork, which introduced the Conway era."
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["Plutus V3 has two additional ", (0,jsx_runtime.jsx)(_components.a, {
        href: "https://plutus.cardano.intersectmbo.org/haddock/master/plutus-ledger-api/PlutusLedgerApi-V3-Contexts.html#t:ScriptPurpose",
        children: "script purposes"
      }), " for validating governance actions: voting and proposing."]
    }), "\n", (0,jsx_runtime.jsx)(_components.p, {
      children: "Additional key differences between Plutus V3 and V1/V2 include:"
    }), "\n", (0,jsx_runtime.jsxs)(_components.ol, {
      children: ["\n", (0,jsx_runtime.jsx)(_components.li, {
        children: "All Plutus V3 scripts, regardless of script purpose, take a single argument: the script context.\nThe datum (for spending scripts) and the redeemer are part of the Plutus V3 script context.\nThis means the same script can be used for spending validation and for different purposes."
      }), "\n", (0,jsx_runtime.jsx)(_components.li, {
        children: "The datum is now optional for spending scripts.\nThe script context may or may not contain a datum, depending on whether the UTXO being spent has a datum associated with it."
      }), "\n", (0,jsx_runtime.jsxs)(_components.li, {
        children: ["There is an additional condition for the evaluation of a Plutus V3 script to be considered successful: the return value must be a ", (0,jsx_runtime.jsx)(_components.code, {
          children: "BuiltinUnit"
        }), "."]
      }), "\n", (0,jsx_runtime.jsxs)(_components.li, {
        children: ["For now, Plutus V3 supports Plutus Core 1.1.0, a Plutus Core language version that introduced ", (0,jsx_runtime.jsx)(_components.a, {
          href: "https://cips.cardano.org/cip/CIP-0085",
          children: "sums-of-products"
        }), ", as well as more builtin functions than Plutus V2.\nHowever, we plan to enable all Plutus Core versions and all builtin functions across all ledger language versions in the future."]
      }), "\n"]
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["The first two points above are attributed to ", (0,jsx_runtime.jsx)(_components.a, {
        href: "https://cips.cardano.org/cip/CIP-69",
        children: "CIP-69"
      }), ", whereas the third point is attributed to ", (0,jsx_runtime.jsx)(_components.a, {
        href: "https://cips.cardano.org/cip/CIP-0117",
        children: "CIP-117"
      }), "."]
    }), "\n", (0,jsx_runtime.jsx)(_components.p, {
      children: "In other words, all Plutus V3 scripts should have the following type in Plinth:"
    }), "\n", (0,jsx_runtime.jsx)(_components.pre, {
      children: (0,jsx_runtime.jsx)(_components.code, {
        className: "language-haskell",
        children: "BuiltinData -> BuiltinUnit\n"
      })
    }), "\n", (0,jsx_runtime.jsx)(_components.p, {
      children: "Updating a Plutus V1/V2 script to turn it into a Plutus V3 script mostly involves straightforward refactoring, except that for a spending script, the case where the datum is absent will need to be handled."
    }), "\n", (0,jsx_runtime.jsx)(_components.hr, {}), "\n", "\n", (0,jsx_runtime.jsxs)(_components.section, {
      "data-footnotes": true,
      className: "footnotes",
      children: [(0,jsx_runtime.jsx)(_components.h2, {
        className: "sr-only",
        id: "footnote-label",
        children: "Footnotes"
      }), "\n", (0,jsx_runtime.jsxs)(_components.ol, {
        children: ["\n", (0,jsx_runtime.jsxs)(_components.li, {
          id: "user-content-fn-1",
          children: ["\n", (0,jsx_runtime.jsxs)(_components.p, {
            children: ["There is one exception to this: Plutus V1 can be used in transactions with reference scripts, even though reference scripts were introduced in the Babbage era. ", (0,jsx_runtime.jsx)(_components.a, {
              href: "#user-content-fnref-1",
              "data-footnote-backref": "",
              "aria-label": "Back to reference 1",
              className: "data-footnote-backref",
              children: "↩"
            })]
          }), "\n"]
        }), "\n", (0,jsx_runtime.jsxs)(_components.li, {
          id: "user-content-fn-2",
          children: ["\n", (0,jsx_runtime.jsxs)(_components.p, {
            children: ["For more information on script purposes, refer to ", (0,jsx_runtime.jsx)(_components.a, {
              href: "/pr-preview/docs/pr-7515/working-with-scripts/script-purposes",
              children: "Script Purposes"
            }), ". ", (0,jsx_runtime.jsx)(_components.a, {
              href: "#user-content-fnref-2",
              "data-footnote-backref": "",
              "aria-label": "Back to reference 2",
              className: "data-footnote-backref",
              children: "↩"
            })]
          }), "\n"]
        }), "\n"]
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