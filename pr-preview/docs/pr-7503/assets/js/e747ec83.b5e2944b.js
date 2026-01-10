"use strict";
(self["webpackChunkdocusaurus"] = self["webpackChunkdocusaurus"] || []).push([[7051],{

/***/ 1637:
/***/ ((__unused_webpack_module, __webpack_exports__, __webpack_require__) => {

// ESM COMPAT FLAG
__webpack_require__.r(__webpack_exports__);

// EXPORTS
__webpack_require__.d(__webpack_exports__, {
  assets: () => (/* binding */ assets),
  contentTitle: () => (/* binding */ contentTitle),
  "default": () => (/* binding */ MDXContent),
  frontMatter: () => (/* binding */ frontMatter),
  metadata: () => (/* reexport */ site_docs_glossary_md_e74_namespaceObject),
  toc: () => (/* binding */ toc)
});

;// ./.docusaurus/docusaurus-plugin-content-docs/default/site-docs-glossary-md-e74.json
const site_docs_glossary_md_e74_namespaceObject = /*#__PURE__*/JSON.parse('{"id":"glossary","title":"Glossary","description":"Address","source":"@site/docs/glossary.md","sourceDirName":".","slug":"/glossary","permalink":"/pr-preview/docs/pr-7503/glossary","draft":false,"unlisted":false,"editUrl":"https://github.com/IntersectMBO/plutus/edit/master/doc/docusaurus/docs/glossary.md","tags":[],"version":"current","sidebarPosition":25,"frontMatter":{"sidebar_position":25},"sidebar":"tutorialSidebar","previous":{"title":"Closing the Auction","permalink":"/pr-preview/docs/pr-7503/auction-smart-contract/end-to-end/closing-the-auction"},"next":{"title":"Haddock Documentation","permalink":"/pr-preview/docs/pr-7503/haddock-documentation"}}');
// EXTERNAL MODULE: ./node_modules/react/jsx-runtime.js
var jsx_runtime = __webpack_require__(4848);
// EXTERNAL MODULE: ./node_modules/@mdx-js/react/lib/index.js
var lib = __webpack_require__(8453);
;// ./docs/glossary.md


const frontMatter = {
	sidebar_position: 25
};
const contentTitle = 'Glossary';

const assets = {

};



const toc = [{
  "value": "Address",
  "id": "address",
  "level": 3
}, {
  "value": "Cardano",
  "id": "cardano",
  "level": 3
}, {
  "value": "Contract Blueprint",
  "id": "contract-blueprint",
  "level": 3
}, {
  "value": "Currency Symbol and Token Name",
  "id": "currency-symbol-and-token-name",
  "level": 3
}, {
  "value": "Datum",
  "id": "datum",
  "level": 3
}, {
  "value": "Extended UTXO Model (EUTXO)",
  "id": "extended-utxo-model-eutxo",
  "level": 3
}, {
  "value": "Guardrail Script",
  "id": "guardrail-script",
  "level": 3
}, {
  "value": "Inline Datum",
  "id": "inline-datum",
  "level": 3
}, {
  "value": "Hard Fork",
  "id": "hard-fork",
  "level": 3
}, {
  "value": "Ledger Era",
  "id": "ledger-era",
  "level": 3
}, {
  "value": "Ledger Language Version",
  "id": "ledger-language-version",
  "level": 3
}, {
  "value": "Minting Policy Script",
  "id": "minting-policy-script",
  "level": 3
}, {
  "value": "Off-chain Code",
  "id": "off-chain-code",
  "level": 3
}, {
  "value": "On-chain Code",
  "id": "on-chain-code",
  "level": 3
}, {
  "value": "Plinth",
  "id": "plinth",
  "level": 3
}, {
  "value": "The Plugin",
  "id": "the-plugin",
  "level": 3
}, {
  "value": "Plutus",
  "id": "plutus",
  "level": 3
}, {
  "value": "Plutus Core",
  "id": "plutus-core",
  "level": 3
}, {
  "value": "Plutus IR",
  "id": "plutus-ir",
  "level": 3
}, {
  "value": "Plutus Metatheory",
  "id": "plutus-metatheory",
  "level": 3
}, {
  "value": "Plutus Script/Validator",
  "id": "plutus-scriptvalidator",
  "level": 3
}, {
  "value": "Plutus Tx",
  "id": "plutus-tx",
  "level": 3
}, {
  "value": "Protocol Parameters",
  "id": "protocol-parameters",
  "level": 3
}, {
  "value": "Protocol Version",
  "id": "protocol-version",
  "level": 3
}, {
  "value": "Redeemer",
  "id": "redeemer",
  "level": 3
}, {
  "value": "Reference Input",
  "id": "reference-input",
  "level": 3
}, {
  "value": "Reference Script",
  "id": "reference-script",
  "level": 3
}, {
  "value": "Scott Encoding",
  "id": "scott-encoding",
  "level": 3
}, {
  "value": "Script Context",
  "id": "script-context",
  "level": 3
}, {
  "value": "Sums of Products",
  "id": "sums-of-products",
  "level": 3
}, {
  "value": "Typed Plutus Core",
  "id": "typed-plutus-core",
  "level": 3
}, {
  "value": "Untyped Plutus Core",
  "id": "untyped-plutus-core",
  "level": 3
}, {
  "value": "UTXO",
  "id": "utxo",
  "level": 3
}];
function _createMdxContent(props) {
  const _components = {
    a: "a",
    code: "code",
    em: "em",
    h1: "h1",
    h3: "h3",
    header: "header",
    li: "li",
    p: "p",
    ul: "ul",
    ...(0,lib/* useMDXComponents */.R)(),
    ...props.components
  };
  return (0,jsx_runtime.jsxs)(jsx_runtime.Fragment, {
    children: [(0,jsx_runtime.jsx)(_components.header, {
      children: (0,jsx_runtime.jsx)(_components.h1, {
        id: "glossary",
        children: "Glossary"
      })
    }), "\n", (0,jsx_runtime.jsx)(_components.h3, {
      id: "address",
      children: "Address"
    }), "\n", (0,jsx_runtime.jsx)(_components.p, {
      children: "Each UTXO has an address, which stipulates the conditions for spending the UTXO."
    }), "\n", (0,jsx_runtime.jsx)(_components.p, {
      children: "An address on Cardano can be based on either a public key hash, which requires a private key signature corresponding to the public key hash to spend the UTXO, or a script hash, which requires the script with that particular hash to be executed to spend the UTXO.\nThese are referred to as public key address and script address, respectively."
    }), "\n", (0,jsx_runtime.jsx)(_components.h3, {
      id: "cardano",
      children: "Cardano"
    }), "\n", (0,jsx_runtime.jsx)(_components.p, {
      children: "The blockchain system for which Plutus Core and Plinth are built."
    }), "\n", (0,jsx_runtime.jsx)(_components.h3, {
      id: "contract-blueprint",
      children: "Contract Blueprint"
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["A contract blueprint enables communication between on-chain code and off-chain code written in different languages.\nIt is introduced in ", (0,jsx_runtime.jsx)(_components.a, {
        href: "https://developers.cardano.org/docs/governance/cardano-improvement-proposals/cip-0057/",
        children: "CIP-57"
      }), ".\nAlso see ", (0,jsx_runtime.jsx)(_components.a, {
        href: "/pr-preview/docs/pr-7503/working-with-scripts/producing-a-blueprint",
        children: "Producing a Plutus Contract Blueprint"
      }), "."]
    }), "\n", (0,jsx_runtime.jsx)(_components.h3, {
      id: "currency-symbol-and-token-name",
      children: "Currency Symbol and Token Name"
    }), "\n", (0,jsx_runtime.jsx)(_components.p, {
      children: "On Cardano, each class of tokens (or asset class) is identified by its currency symbol (also known as currency, or asset group) along with the token name.\nThe minting and burning of a token are controlled by the Plutus script whose hash corresponds to the token's currency symbol."
    }), "\n", (0,jsx_runtime.jsx)(_components.p, {
      children: "Ada/Lovelace is a special asset class where the currency symbol and token name are both empty strings, and it cannot be minted or burned via transactions."
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["See ", (0,jsx_runtime.jsx)(_components.a, {
        href: "https://iohk.io/en/research/library/papers/utxomautxo-with-multi-asset-support/",
        children: (0,jsx_runtime.jsx)(_components.em, {
          children: "UTXOma: UTXO with Multi-Asset Support"
        })
      }), "."]
    }), "\n", (0,jsx_runtime.jsx)(_components.h3, {
      id: "datum",
      children: "Datum"
    }), "\n", (0,jsx_runtime.jsx)(_components.p, {
      children: "A piece of data attached to a UTXO at a script address.\nThe datum serves as an input to the script, and is often used to represent the state of a smart contract."
    }), "\n", (0,jsx_runtime.jsx)(_components.h3, {
      id: "extended-utxo-model-eutxo",
      children: "Extended UTXO Model (EUTXO)"
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["An extended version of the UTXO model, where each UTXO can carry additional data (or \"datum\"), and be associated with a Plutus script that specifies the conditions under which the UTXO can be spent.\nSee ", (0,jsx_runtime.jsx)(_components.a, {
        href: "https://iohk.io/en/research/library/papers/the-extended-utxo-model/",
        children: (0,jsx_runtime.jsx)(_components.em, {
          children: "The Extended UTXO Model"
        })
      }), "."]
    }), "\n", (0,jsx_runtime.jsx)(_components.h3, {
      id: "guardrail-script",
      children: "Guardrail Script"
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["A guardrail script, sometimes referred to as a constitution script or a proposing script, is a Plutus V3 script used to validate two kinds of governance actions: parameter change and treasury withdrawal.\nSee ", (0,jsx_runtime.jsx)(_components.a, {
        href: "/pr-preview/docs/pr-7503/working-with-scripts/script-purposes",
        children: "Script Purposes"
      }), "."]
    }), "\n", (0,jsx_runtime.jsx)(_components.h3, {
      id: "inline-datum",
      children: "Inline Datum"
    }), "\n", (0,jsx_runtime.jsx)(_components.p, {
      children: "Inline datums are a feature introduced in the Babbage era.\nBefore babbage, a UTXO could only contain a datum hash, not the datum itself.\nTo spend such a UTXO, the corresponding datum must be provided in the transaction.\nInline datums allow datums to be directly attached to UTXOs."
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["For more details, see ", (0,jsx_runtime.jsx)(_components.a, {
        href: "https://cips.cardano.org/cip/CIP-32",
        children: "CIP-32"
      }), "."]
    }), "\n", (0,jsx_runtime.jsx)(_components.h3, {
      id: "hard-fork",
      children: "Hard Fork"
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["A hard fork is an update of the major protocol version, i.e., transitioning the protocol version from ", (0,jsx_runtime.jsx)(_components.code, {
        children: "x.y"
      }), " to ", (0,jsx_runtime.jsx)(_components.code, {
        children: "x+1.0"
      }), ".\nA hard fork is required when a backwards incompatible change to the Cardano node is made, causing the old node to reject some blocks produced by the new node.\nAs a result, old nodes are no longer able to validate the chain, and all participants must upgrade to the new version.\nA hard fork is initiated by a transaction that updates the protocol version.\nThe protocoal version is one of the protocol parameters, and like other protocol parameter changes, a hard fork always takes effect at an epoch boundary."]
    }), "\n", (0,jsx_runtime.jsx)(_components.p, {
      children: "A hard fork may or may not introduce a new ledger era.\nThe latter is called an intra-era hard fork.\nFor example, the Vasil hard fork introduced the Babbage era, and the Chang hard fork introduced the Conway era.\nThe Valentine hard fork is an example of an intra-era hard fork."
    }), "\n", (0,jsx_runtime.jsx)(_components.h3, {
      id: "ledger-era",
      children: "Ledger Era"
    }), "\n", (0,jsx_runtime.jsx)(_components.p, {
      children: "A ledger era marks a specific period where new features are added to the Cardano ledger, for instance"
    }), "\n", (0,jsx_runtime.jsxs)(_components.ul, {
      children: ["\n", (0,jsx_runtime.jsx)(_components.li, {
        children: "The Alonzo era, which followed the Alonzo hard fork, introduced smart contracts and Plutus V1."
      }), "\n", (0,jsx_runtime.jsx)(_components.li, {
        children: "The Babbage era, which followed the Vasil hard fork, introduced Plutus V2 along with features such as reference scripts and inline datum."
      }), "\n", (0,jsx_runtime.jsx)(_components.li, {
        children: "The Conway era, which followed the Chang hard fork, introduced Plutus V3 and features such as governance actions and voting."
      }), "\n"]
    }), "\n", (0,jsx_runtime.jsx)(_components.p, {
      children: "A hard fork is required to introduce a new ledger era, but a hard fork does not necessarily introduce a new ledger era."
    }), "\n", (0,jsx_runtime.jsx)(_components.h3, {
      id: "ledger-language-version",
      children: "Ledger Language Version"
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["This is what \"Plutus V1\", \"Plutus V2\", \"Plutus V3\" refer to.\nSee ", (0,jsx_runtime.jsx)(_components.a, {
        href: "./essential-concepts/versions",
        children: "Different Notions of Version"
      }), " and ", (0,jsx_runtime.jsx)(_components.a, {
        href: "./working-with-scripts/ledger-language-version",
        children: "Plutus Ledger Language Version"
      }), "."]
    }), "\n", (0,jsx_runtime.jsx)(_components.h3, {
      id: "minting-policy-script",
      children: "Minting Policy Script"
    }), "\n", (0,jsx_runtime.jsx)(_components.p, {
      children: "A Plutus script which must be satisfied in order for a transaction to mint tokens of the corresponding currency."
    }), "\n", (0,jsx_runtime.jsx)(_components.h3, {
      id: "off-chain-code",
      children: "Off-chain Code"
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["Code executed by individual applications rather than Cardano nodes.\nThis includes functions like building, signing, and submitting transactions.\nOff-chain code can be developed using libraries like ", (0,jsx_runtime.jsx)(_components.a, {
        href: "https://meshjs.dev/",
        children: "Mesh"
      }), ", ", (0,jsx_runtime.jsx)(_components.a, {
        href: "https://pycardano.readthedocs.io/en/latest/",
        children: "PyCardano"
      }), " and ", (0,jsx_runtime.jsx)(_components.a, {
        href: "https://github.com/IntersectMBO/cardano-api",
        children: "Cardano API"
      }), "."]
    }), "\n", (0,jsx_runtime.jsx)(_components.h3, {
      id: "on-chain-code",
      children: "On-chain Code"
    }), "\n", (0,jsx_runtime.jsx)(_components.p, {
      children: "Code executed directly on the Cardano blockchain by each participating node.\nThe main function of on-chain code is for nodes to validate transactions, such as checking if a transaction is permitted to spend a UTXO or mint a token.\nOn-chain code is usually written in a high level language like Plinth, and compiled into Untyped Plutus Core (UPLC).\nThe Cardano node includes an evaluator that runs UPLC programs."
    }), "\n", (0,jsx_runtime.jsx)(_components.h3, {
      id: "plinth",
      children: "Plinth"
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["is a high-level language for writing the validation logic of transactions. See ", (0,jsx_runtime.jsx)(_components.a, {
        href: "/pr-preview/docs/pr-7503/essential-concepts/plinth-and-plutus-core",
        children: "Plinth and Plutus Core"
      }), "."]
    }), "\n", (0,jsx_runtime.jsx)(_components.h3, {
      id: "the-plugin",
      children: "The Plugin"
    }), "\n", (0,jsx_runtime.jsx)(_components.p, {
      children: "The compiler from Plinth to Untyped Plutus Core, which is implemented as a GHC plugin."
    }), "\n", (0,jsx_runtime.jsx)(_components.h3, {
      id: "plutus",
      children: "Plutus"
    }), "\n", (0,jsx_runtime.jsx)(_components.p, {
      children: "The term \"Plutus\" can refer to Untyped Plutus Core, Typed Plutus Core, or, prior to its renaming to Plinth, Plutus Tx.\nTo minimize confusion, the term \"Plutus\" on its own should either be avoided or used exclusively to refer to Untyped Plutus Core."
    }), "\n", (0,jsx_runtime.jsx)(_components.h3, {
      id: "plutus-core",
      children: "Plutus Core"
    }), "\n", (0,jsx_runtime.jsx)(_components.p, {
      children: "The term \"Plutus Core\" can refer either to Untyped Plutus Core or Typed Plutus Core, depending on the context.\nTo avoid confusion, it is recommended to use UPLC for Untyped Plutus Core and TPLC for Typed Plutus Core."
    }), "\n", (0,jsx_runtime.jsx)(_components.h3, {
      id: "plutus-ir",
      children: "Plutus IR"
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["An intermediate language that compiles to Plutus Core.\nSee ", (0,jsx_runtime.jsx)(_components.a, {
        href: "/pr-preview/docs/pr-7503/essential-concepts/plinth-and-plutus-core",
        children: "Plinth and Plutus Core"
      }), "."]
    }), "\n", (0,jsx_runtime.jsx)(_components.h3, {
      id: "plutus-metatheory",
      children: "Plutus Metatheory"
    }), "\n", (0,jsx_runtime.jsx)(_components.p, {
      children: "The formalization of typed and untyped Plutus Core.\nIn the future we may add Plutus IR to the formalization.\nIt is \"meta\" in the sense that it is a framework for reasoning about the Plutus Core languages themselves."
    }), "\n", (0,jsx_runtime.jsx)(_components.h3, {
      id: "plutus-scriptvalidator",
      children: "Plutus Script/Validator"
    }), "\n", (0,jsx_runtime.jsx)(_components.p, {
      children: "A Plutus script, or Plutus validator, is a UPLC program executed on-chain.\nSometimes a program written in a high level language that compiles to UPLC, such as Plinth, is also referred to as a Plutus script."
    }), "\n", (0,jsx_runtime.jsx)(_components.h3, {
      id: "plutus-tx",
      children: "Plutus Tx"
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["Plutus Tx was the former name of Plinth. See ", (0,jsx_runtime.jsx)(_components.a, {
        href: "/pr-preview/docs/pr-7503/essential-concepts/plinth-and-plutus-core",
        children: "Plinth and Plutus Core"
      }), "."]
    }), "\n", (0,jsx_runtime.jsx)(_components.h3, {
      id: "protocol-parameters",
      children: "Protocol Parameters"
    }), "\n", (0,jsx_runtime.jsx)(_components.p, {
      children: "Various settings that control the behavior of the Cardano blockchain."
    }), "\n", (0,jsx_runtime.jsx)(_components.h3, {
      id: "protocol-version",
      children: "Protocol Version"
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["A key protocol parameter that indicates the current version of the blockchain protocol in use.\nIt is in the form of ", (0,jsx_runtime.jsx)(_components.code, {
        children: "x.y"
      }), ", where ", (0,jsx_runtime.jsx)(_components.code, {
        children: "x"
      }), " is the major protocol version and ", (0,jsx_runtime.jsx)(_components.code, {
        children: "y"
      }), " is the minor protocol version.\nA hard fork bumps the major protocol version, while a soft fork bumps the minor protocol version."]
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["Protocol versions are closely tied to Cardano node versions.\nA node of major version ", (0,jsx_runtime.jsx)(_components.code, {
        children: "x"
      }), " supports up to major protocol version ", (0,jsx_runtime.jsx)(_components.code, {
        children: "x"
      }), ".\nThus after a hard fork that bumps the major protocol version to ", (0,jsx_runtime.jsx)(_components.code, {
        children: "x+1"
      }), ", node version ", (0,jsx_runtime.jsx)(_components.code, {
        children: "x"
      }), " or older will become obsolete, requiring all participants to upgrade their nodes."]
    }), "\n", (0,jsx_runtime.jsx)(_components.h3, {
      id: "redeemer",
      children: "Redeemer"
    }), "\n", (0,jsx_runtime.jsx)(_components.p, {
      children: "A piece of data included in a transaction that serves as an input to a Plutus script that needs to be executed to validate this transaction."
    }), "\n", (0,jsx_runtime.jsx)(_components.p, {
      children: "If a smart contract is regarded as a state machine, the redeemer would be the input that ticks the state machine."
    }), "\n", (0,jsx_runtime.jsx)(_components.h3, {
      id: "reference-input",
      children: "Reference Input"
    }), "\n", (0,jsx_runtime.jsx)(_components.p, {
      children: "Reference inputs are a feature introduced in the Babbage era.\nA reference input is a UTXO that a transaction can inspect without having to consume it.\nRecall that a UTXO can only be consumed once.\nSince a UTXO can only be consumed once, reference inputs help avoid the need to keep consuming and recreating similar UTXOs."
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["For more details, see ", (0,jsx_runtime.jsx)(_components.a, {
        href: "https://cips.cardano.org/cip/CIP-31",
        children: "CIP-31"
      }), "."]
    }), "\n", (0,jsx_runtime.jsx)(_components.h3, {
      id: "reference-script",
      children: "Reference Script"
    }), "\n", (0,jsx_runtime.jsx)(_components.p, {
      children: "Reference scripts are a feature introduced in the Babbage era.\nBefore Babbage, a UTXO could not contain scripts, so spending a UTXO with a script address required the script to be included in the transaction.\nReference scripts allow scripts to be attached to UTXOs, which can then be used as reference inputs.\nThis reduces transaction sizes, and avoids the need to include the same scripts in multiple transactions."
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["For more details, see ", (0,jsx_runtime.jsx)(_components.a, {
        href: "https://cips.cardano.org/cip/CIP-33",
        children: "CIP-33"
      }), "."]
    }), "\n", (0,jsx_runtime.jsx)(_components.h3, {
      id: "scott-encoding",
      children: "Scott Encoding"
    }), "\n", (0,jsx_runtime.jsx)(_components.p, {
      children: "Scott encoding is a method for encoding datatypes in lambda calculus.\nThe Plinth compiler adopts Scott encoding for Plinth datatypes when compiling to Plutus Core 1.0.0.\nWhen compiling to Plutus Core 1.1.0, sums of products is used instead, which makes scripts smaller and cheaper compared to Scott encoding.\nCurrently, Plutus V1 and V2 are only compatible with Plutus Core 1.0.0, whereas Plutus V3 is also compatible with Plutus Core 1.1.0.\nHowever, we plan to make all Plutus ledger language versions compatible with all Plutus Core versions in the future."
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["For more details, see the ", (0,jsx_runtime.jsx)(_components.a, {
        href: "https://en.wikipedia.org/wiki/Mogensen%E2%80%93Scott_encoding",
        children: "Wikipedia page"
      }), " on Scott encoding."]
    }), "\n", (0,jsx_runtime.jsx)(_components.h3, {
      id: "script-context",
      children: "Script Context"
    }), "\n", (0,jsx_runtime.jsx)(_components.p, {
      children: "An input to a Plutus script created by the ledger.\nIt includes details of the transaction being validated.\nAdditionally, since a transaction may do multiple things, each of which needs to be validated by a separate script, the script context also specifies what exactly the current script is responsible for validating."
    }), "\n", (0,jsx_runtime.jsx)(_components.h3, {
      id: "sums-of-products",
      children: "Sums of Products"
    }), "\n", (0,jsx_runtime.jsx)(_components.p, {
      children: "Sums of products is an alternative method to Scott encoding for encoding datatypes.\nThe Plutus Core language supports sums of products since version 1.1.0.\nCurrently, Plutus Core 1.1.0 is only compatible with Plutus V3, but we plan to make it compatible with Plutus V1 and V2 in the future."
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["For more details, see ", (0,jsx_runtime.jsx)(_components.a, {
        href: "https://cips.cardano.org/cip/CIP-0085",
        children: "CIP-85"
      }), "."]
    }), "\n", (0,jsx_runtime.jsx)(_components.h3, {
      id: "typed-plutus-core",
      children: "Typed Plutus Core"
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["The typed counterpart of Untyped Plutus Core, and can serve as a low-level IR for compilers targeting Untyped Plutus Core.\nSee ", (0,jsx_runtime.jsx)(_components.a, {
        href: "/pr-preview/docs/pr-7503/essential-concepts/plinth-and-plutus-core",
        children: "Plinth and Plutus Core"
      }), "."]
    }), "\n", (0,jsx_runtime.jsx)(_components.h3, {
      id: "untyped-plutus-core",
      children: "Untyped Plutus Core"
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["A low-level language for on-chain code, based on untyped lambda calculus, a well-studied formalism for computing.\nSee ", (0,jsx_runtime.jsx)(_components.a, {
        href: "/pr-preview/docs/pr-7503/essential-concepts/plinth-and-plutus-core",
        children: "Plinth and Plutus Core"
      }), "."]
    }), "\n", (0,jsx_runtime.jsx)(_components.h3, {
      id: "utxo",
      children: "UTXO"
    }), "\n", (0,jsx_runtime.jsx)(_components.p, {
      children: "UTXO stands for unspent transaction output.\nCardano adopts the UTXO model, one of the two popular ledger models for blockchains, the other one being the account model."
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