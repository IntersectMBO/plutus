"use strict";
(self["webpackChunkdocusaurus"] = self["webpackChunkdocusaurus"] || []).push([[2982],{

/***/ 7395:
/***/ ((__unused_webpack_module, __webpack_exports__, __webpack_require__) => {

// ESM COMPAT FLAG
__webpack_require__.r(__webpack_exports__);

// EXPORTS
__webpack_require__.d(__webpack_exports__, {
  assets: () => (/* binding */ assets),
  contentTitle: () => (/* binding */ contentTitle),
  "default": () => (/* binding */ MDXContent),
  frontMatter: () => (/* binding */ frontMatter),
  metadata: () => (/* reexport */ site_docs_essential_concepts_plutus_core_and_plutus_tx_md_c02_namespaceObject),
  toc: () => (/* binding */ toc)
});

;// ./.docusaurus/docusaurus-plugin-content-docs/default/site-docs-essential-concepts-plutus-core-and-plutus-tx-md-c02.json
const site_docs_essential_concepts_plutus_core_and_plutus_tx_md_c02_namespaceObject = /*#__PURE__*/JSON.parse('{"id":"essential-concepts/plutus-core-and-plutus-tx","title":"Plutus Core and Plutus Tx","description":"Understanding the roles and relationships between different languages is key to the effective and efficient development of smart contracts.","source":"@site/docs/essential-concepts/plutus-core-and-plutus-tx.md","sourceDirName":"essential-concepts","slug":"/essential-concepts/plutus-core-and-plutus-tx","permalink":"/docs/essential-concepts/plutus-core-and-plutus-tx","draft":false,"unlisted":false,"editUrl":"https://github.com/IntersectMBO/plutus/edit/master/doc/docusaurus/docs/essential-concepts/plutus-core-and-plutus-tx.md","tags":[],"version":"current","sidebarPosition":5,"frontMatter":{"sidebar_position":5},"sidebar":"tutorialSidebar","previous":{"title":"Essential concepts","permalink":"/docs/category/essential-concepts"},"next":{"title":"Different Notions of Version","permalink":"/docs/essential-concepts/versions"}}');
// EXTERNAL MODULE: ./node_modules/react/jsx-runtime.js
var jsx_runtime = __webpack_require__(4848);
// EXTERNAL MODULE: ./node_modules/@mdx-js/react/lib/index.js
var lib = __webpack_require__(8453);
;// ./docs/essential-concepts/plutus-core-and-plutus-tx.md


const frontMatter = {
	sidebar_position: 5
};
const contentTitle = 'Plutus Core and Plutus Tx';

const assets = {

};



const toc = [{
  "value": "Untyped Plutus Core",
  "id": "untyped-plutus-core",
  "level": 2
}, {
  "value": "Typed Plutus Core and Plutus IR",
  "id": "typed-plutus-core-and-plutus-ir",
  "level": 3
}, {
  "value": "Plutus Tx",
  "id": "plutus-tx",
  "level": 2
}, {
  "value": "Further reading",
  "id": "further-reading",
  "level": 2
}];
function _createMdxContent(props) {
  const _components = {
    a: "a",
    em: "em",
    h1: "h1",
    h2: "h2",
    h3: "h3",
    header: "header",
    p: "p",
    ...(0,lib/* useMDXComponents */.R)(),
    ...props.components
  };
  return (0,jsx_runtime.jsxs)(jsx_runtime.Fragment, {
    children: [(0,jsx_runtime.jsx)(_components.header, {
      children: (0,jsx_runtime.jsx)(_components.h1, {
        id: "plutus-core-and-plutus-tx",
        children: "Plutus Core and Plutus Tx"
      })
    }), "\n", (0,jsx_runtime.jsx)(_components.p, {
      children: "Understanding the roles and relationships between different languages is key to the effective and efficient development of smart contracts."
    }), "\n", (0,jsx_runtime.jsx)(_components.h2, {
      id: "untyped-plutus-core",
      children: "Untyped Plutus Core"
    }), "\n", (0,jsx_runtime.jsx)(_components.p, {
      children: "Untyped Plutus Core (UPLC), also known simply as Plutus Core or Plutus, is a low-level, Turing-complete language based on untyped lambda calculus, a simple and well-established computational model that dates back to the 1930s.\nThanks to its simplicity and extensive academic research, the need for updates or modifications to the language over time is minimal, ensuring long-term stability.\nIt also facilitates the creation of simple, formally verified evaluators."
    }), "\n", (0,jsx_runtime.jsx)(_components.p, {
      children: "Along with UPLC and its evaluator, we provide a compiler from Plutus Tx, a subset of Haskell, to UPLC.\nHowever, UPLC can be an easy compilation target for any language that supports functional-style programming, in particular immutable data and higher-order functions, both of which are widely adopted today in programming languages, and are particularly suited to Cardano's UTXO ledger model, where UTXOs are immutable."
    }), "\n", (0,jsx_runtime.jsx)(_components.p, {
      children: "UPLC is the code that runs on-chain, i.e., by every node validating the transaction, using an interpreter known as the CEK machine.\nA UPLC program included in a Cardano transaction is often referred to as a Plutus script or a Plutus validator."
    }), "\n", (0,jsx_runtime.jsx)(_components.h3, {
      id: "typed-plutus-core-and-plutus-ir",
      children: "Typed Plutus Core and Plutus IR"
    }), "\n", (0,jsx_runtime.jsx)(_components.p, {
      children: "Typed Plutus Core (TPLC) is the intrinsically typed counterpart of UPLC.\nIt is based on higher-order polymorphic lambda calculus with isorecursive types (System Fωμ).\nTPLC serves as a low-level intermediate representation (IR) for the Plutus Tx compiler.\nTPLC is closely related to UPLC, and compiling TPLC into UPLC is simply a matter of erasing types."
    }), "\n", (0,jsx_runtime.jsx)(_components.p, {
      children: "Plutus IR (PIR) is a high-level IR also used by the Plutus Tx compiler.\nIt extends TPLC by adding recursive bindings and recursive data types.\nThe fact that recursion is explicit in PIR, rather than encoded using fixed point operators as in TPLC and UPLC, makes PIR significantly more readable than TPLC and UPLC.\nWhen optimizing the cost or size of Plutus scripts written in Plutus Tx, it is usually useful to look into PIR."
    }), "\n", (0,jsx_runtime.jsx)(_components.h2, {
      id: "plutus-tx",
      children: "Plutus Tx"
    }), "\n", (0,jsx_runtime.jsx)(_components.p, {
      children: "Plutus Tx, the primary focus of this user guide, is a high-level language for writing the validation logic of the contract, the logic that determines whether a transaction is allowed to perform things such as spending a UTXO, minting or burning assets, and more.\nPlutus Tx is not a new language, but rather a subset of Haskell, and it is compiled into UPLC."
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["There are several other high-level languages available as alternatives to Plutus Tx, all of which compile to UPLC.\nSee ", (0,jsx_runtime.jsx)(_components.a, {
        href: "/docs/delve-deeper/languages",
        children: "Overview of Languages Compiling to UPLC"
      }), " for more information."]
    }), "\n", (0,jsx_runtime.jsx)(_components.h2, {
      id: "further-reading",
      children: "Further reading"
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["The formal details of Plutus Core are in its ", (0,jsx_runtime.jsx)(_components.a, {
        href: "https://github.com/IntersectMBO/plutus#specifications-and-design",
        children: "specification"
      }), "."]
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["PIR is discussed in ", (0,jsx_runtime.jsx)(_components.a, {
        href: "https://iohk.io/en/research/library/papers/unraveling-recursion-compiling-an-ir-with-recursion-to-system-f/",
        children: (0,jsx_runtime.jsx)(_components.em, {
          children: "Unraveling recursion: compiling an IR with recursion to System F"
        })
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