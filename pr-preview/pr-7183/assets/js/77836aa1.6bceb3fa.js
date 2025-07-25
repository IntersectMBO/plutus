"use strict";
(self["webpackChunkdocusaurus"] = self["webpackChunkdocusaurus"] || []).push([[5807],{

/***/ 5571:
/***/ ((__unused_webpack_module, __webpack_exports__, __webpack_require__) => {

// ESM COMPAT FLAG
__webpack_require__.r(__webpack_exports__);

// EXPORTS
__webpack_require__.d(__webpack_exports__, {
  assets: () => (/* binding */ assets),
  contentTitle: () => (/* binding */ contentTitle),
  "default": () => (/* binding */ MDXContent),
  frontMatter: () => (/* binding */ frontMatter),
  metadata: () => (/* reexport */ site_docs_essential_concepts_eutxo_md_778_namespaceObject),
  toc: () => (/* binding */ toc)
});

;// ./.docusaurus/docusaurus-plugin-content-docs/default/site-docs-essential-concepts-eutxo-md-778.json
const site_docs_essential_concepts_eutxo_md_778_namespaceObject = /*#__PURE__*/JSON.parse('{"id":"essential-concepts/eutxo","title":"Scripts and the Extended UTXO Model","description":"Account-based and UTXO-based Ledgers","source":"@site/docs/essential-concepts/eutxo.md","sourceDirName":"essential-concepts","slug":"/essential-concepts/eutxo","permalink":"/docs/essential-concepts/eutxo","draft":false,"unlisted":false,"editUrl":"https://github.com/IntersectMBO/plutus/edit/master/doc/docusaurus/docs/essential-concepts/eutxo.md","tags":[],"version":"current","sidebarPosition":20,"frontMatter":{"sidebar_position":20},"sidebar":"tutorialSidebar","previous":{"title":"Different Notions of Version","permalink":"/docs/essential-concepts/versions"},"next":{"title":"Example: An Auction Smart Contract","permalink":"/docs/category/example-an-auction-smart-contract"}}');
// EXTERNAL MODULE: ./node_modules/react/jsx-runtime.js
var jsx_runtime = __webpack_require__(4848);
// EXTERNAL MODULE: ./node_modules/@mdx-js/react/lib/index.js
var lib = __webpack_require__(8453);
;// ./docs/essential-concepts/eutxo.md


const frontMatter = {
	sidebar_position: 20
};
const contentTitle = 'Scripts and the Extended UTXO Model';

const assets = {

};



const toc = [{
  "value": "Account-based and UTXO-based Ledgers",
  "id": "account-based-and-utxo-based-ledgers",
  "level": 2
}, {
  "value": "The Extended UTXO Model",
  "id": "the-extended-utxo-model",
  "level": 2
}];
function _createMdxContent(props) {
  const _components = {
    a: "a",
    h1: "h1",
    h2: "h2",
    header: "header",
    p: "p",
    table: "table",
    tbody: "tbody",
    td: "td",
    th: "th",
    thead: "thead",
    tr: "tr",
    ...(0,lib/* useMDXComponents */.R)(),
    ...props.components
  };
  return (0,jsx_runtime.jsxs)(jsx_runtime.Fragment, {
    children: [(0,jsx_runtime.jsx)(_components.header, {
      children: (0,jsx_runtime.jsx)(_components.h1, {
        id: "scripts-and-the-extended-utxo-model",
        children: "Scripts and the Extended UTXO Model"
      })
    }), "\n", (0,jsx_runtime.jsx)(_components.h2, {
      id: "account-based-and-utxo-based-ledgers",
      children: "Account-based and UTXO-based Ledgers"
    }), "\n", (0,jsx_runtime.jsx)(_components.p, {
      children: "There are two dominant paradigms for implementing distributed ledgers that manage and track the ownership of assets.\nThe first, account-based ledgers, model the system as a list of mutable accounts, as in"
    }), "\n", (0,jsx_runtime.jsxs)(_components.table, {
      children: [(0,jsx_runtime.jsx)(_components.thead, {
        children: (0,jsx_runtime.jsxs)(_components.tr, {
          children: [(0,jsx_runtime.jsx)(_components.th, {
            children: "Owner"
          }), (0,jsx_runtime.jsx)(_components.th, {
            children: "Balance"
          })]
        })
      }), (0,jsx_runtime.jsxs)(_components.tbody, {
        children: [(0,jsx_runtime.jsxs)(_components.tr, {
          children: [(0,jsx_runtime.jsx)(_components.td, {
            children: "Alice"
          }), (0,jsx_runtime.jsx)(_components.td, {
            children: "43 USD"
          })]
        }), (0,jsx_runtime.jsxs)(_components.tr, {
          children: [(0,jsx_runtime.jsx)(_components.td, {
            children: "Bob"
          }), (0,jsx_runtime.jsx)(_components.td, {
            children: "12 USD"
          })]
        })]
      })]
    }), "\n", (0,jsx_runtime.jsx)(_components.p, {
      children: "A transaction can decrease the balance of the sender, and increase the balance of the recipient."
    }), "\n", (0,jsx_runtime.jsx)(_components.p, {
      children: "Account-based ledgers, such as Ethereum, are relatively simple to implement, but they have disadvantages due to the fact that the state of an account is global: all transactions that do anything with an account must touch this one value.\nThis can lead to issues with throughput, as well as ordering issues (if Alice sends 5 USD to Bob, and Bob sends 5 USD to Carol, this may succeed or fail depending on the order in which the transactions are processed)."
    }), "\n", (0,jsx_runtime.jsx)(_components.p, {
      children: "The second paradigm is UTXO-based ledgers, such as Bitcoin, which represent the state of the ledger as a set of unspent\ntransaction outputs (UTXOs).\nA UTXO is like an envelope with some money in it: it is addressed to a particular party, and it contains some assets.\nA transaction spends some number of UTXOs, and creates new ones.\nA UTXO is immutable and can only be spent once."
    }), "\n", (0,jsx_runtime.jsx)(_components.p, {
      children: "So a transaction that sends 5 USD from Alice to Bob would do so by spending some number of already existing UTXOs belonging to Alice, and creating a new UTXO with 5 USD belonging to Bob."
    }), "\n", (0,jsx_runtime.jsx)(_components.p, {
      children: "UTXO-based ledgers are more complicated, but avoid some of the issues of account-based ledgers, since any transaction deals only with the inputs that it spends.\nCardano is a UTXO-based ledger."
    }), "\n", (0,jsx_runtime.jsx)(_components.h2, {
      id: "the-extended-utxo-model",
      children: "The Extended UTXO Model"
    }), "\n", (0,jsx_runtime.jsx)(_components.p, {
      children: "In the classic UTXO model, each UTXO's address includes a public key (strictly, the hash of a public key), and in order to spend this output, the spending transaction must be signed by the corresponding private key.\nWe call this UTXO a public key UTXO, and its address a public key address."
    }), "\n", (0,jsx_runtime.jsx)(_components.p, {
      children: "Cardano uses an extended model called the Extended UTXO Model (EUTXO).\nIn the EUTXO model, a UTXO's address may include the hash of a script.\nWe call this UTXO a script UTXO, and its address a script address."
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["Spending a script UTXO does not require a signature, but instead, requires the script whose hash matches the UTXO address to be included either directly in the transaction, or in a reference input referenced by the transaction.\nThe script runs to determine if the transaction is authorized to spend the UTXO.\nScripts can also validate other actions transactions perform, such as minting and burning tokens, withdrawing staking rewards, voting, and more.\nFor further details, see ", (0,jsx_runtime.jsx)(_components.a, {
        href: "/docs/working-with-scripts/script-purposes",
        children: "Script Purposes"
      }), "."]
    }), "\n", (0,jsx_runtime.jsx)(_components.p, {
      children: "A simple script would be one that checks whether the spending transaction is signed by a particular public key.\nThis would mirror the functionality of simple public key outputs.\nHowever, scripts allow us to implement a wide range of useful logic on the blockchain."
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["To learn more about writing scripts, see ", (0,jsx_runtime.jsx)(_components.a, {
        href: "../category/using-plinth",
        children: "Using Plinth"
      }), " and ", (0,jsx_runtime.jsx)(_components.a, {
        href: "../category/working-with-scripts",
        children: "Working with scripts"
      }), "."]
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