"use strict";
(self["webpackChunkdocusaurus"] = self["webpackChunkdocusaurus"] || []).push([[564],{

/***/ 1104:
/***/ ((__unused_webpack_module, __webpack_exports__, __webpack_require__) => {

// ESM COMPAT FLAG
__webpack_require__.r(__webpack_exports__);

// EXPORTS
__webpack_require__.d(__webpack_exports__, {
  assets: () => (/* binding */ assets),
  contentTitle: () => (/* binding */ contentTitle),
  "default": () => (/* binding */ MDXContent),
  frontMatter: () => (/* binding */ frontMatter),
  metadata: () => (/* reexport */ site_docs_essential_concepts_plinth_and_plutus_core_md_6df_namespaceObject),
  toc: () => (/* binding */ toc)
});

;// ./.docusaurus/docusaurus-plugin-content-docs/default/site-docs-essential-concepts-plinth-and-plutus-core-md-6df.json
const site_docs_essential_concepts_plinth_and_plutus_core_md_6df_namespaceObject = /*#__PURE__*/JSON.parse('{"id":"essential-concepts/plinth-and-plutus-core","title":"Plinth and Plutus Core","description":"Understanding the roles and relationships between different languages is key to the effective and efficient development of smart contracts.","source":"@site/docs/essential-concepts/plinth-and-plutus-core.md","sourceDirName":"essential-concepts","slug":"/essential-concepts/plinth-and-plutus-core","permalink":"/pr-preview/docs/pr-7440/essential-concepts/plinth-and-plutus-core","draft":false,"unlisted":false,"editUrl":"https://github.com/IntersectMBO/plutus/edit/master/doc/docusaurus/docs/essential-concepts/plinth-and-plutus-core.md","tags":[],"version":"current","sidebarPosition":5,"frontMatter":{"sidebar_position":5},"sidebar":"tutorialSidebar","previous":{"title":"Essential concepts","permalink":"/pr-preview/docs/pr-7440/category/essential-concepts"},"next":{"title":"Different Notions of Version","permalink":"/pr-preview/docs/pr-7440/essential-concepts/versions"}}');
// EXTERNAL MODULE: ./node_modules/react/jsx-runtime.js
var jsx_runtime = __webpack_require__(4848);
// EXTERNAL MODULE: ./node_modules/@mdx-js/react/lib/index.js
var lib = __webpack_require__(8453);
;// ./docs/essential-concepts/plinth-and-plutus-core.md


const frontMatter = {
	sidebar_position: 5
};
const contentTitle = 'Plinth and Plutus Core';

const assets = {

};



const toc = [{
  "value": "Plinth (formerly Plutus Tx)",
  "id": "plinth-formerly-plutus-tx",
  "level": 2
}, {
  "value": "Untyped Plutus Core",
  "id": "untyped-plutus-core",
  "level": 2
}, {
  "value": "Typed Plutus Core and Plutus IR",
  "id": "typed-plutus-core-and-plutus-ir",
  "level": 3
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
        id: "plinth-and-plutus-core",
        children: "Plinth and Plutus Core"
      })
    }), "\n", (0,jsx_runtime.jsx)(_components.p, {
      children: "Understanding the roles and relationships between different languages is key to the effective and efficient development of smart contracts."
    }), "\n", (0,jsx_runtime.jsx)(_components.h2, {
      id: "plinth-formerly-plutus-tx",
      children: "Plinth (formerly Plutus Tx)"
    }), "\n", (0,jsx_runtime.jsx)(_components.p, {
      children: "Plinth, the primary focus of this user guide, is a high-level language for writing the validation logic of the contract, the logic that determines whether a transaction is allowed to perform things such as spending a UTXO, minting or burning assets, and more.\nPlinth is not a new language, but rather a subset of Haskell, and it is compiled into Untyped Plutus Core (UPLC)."
    }), "\n", (0,jsx_runtime.jsx)(_components.p, {
      children: "Plinth was previously known as Plutus Tx.\nIt was renamed to avoid confusion around the term \"Plutus\", which has been used ambiguously to refer to both \"Plutus Tx\" and \"Plutus Core\".\nThis led to misunderstandings - particularly the incorrect assumption that Cardano uses a Haskell-based language for on-chain execution."
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["In reality, the on-chain language is Untyped Plutus Core, a low-level language based on lambda calculus.\nPlinth is one of several high-level languages that compile to it, alongside other alternatives.\nSee ", (0,jsx_runtime.jsx)(_components.a, {
        href: "/pr-preview/docs/pr-7440/delve-deeper/languages",
        children: "Overview of Languages Compiling to UPLC"
      }), " for more details."]
    }), "\n", (0,jsx_runtime.jsx)(_components.p, {
      children: "To minimize confusion, the term \"Plutus\" on its own should either be avoided or used exclusively to refer to Untyped Plutus Core."
    }), "\n", (0,jsx_runtime.jsx)(_components.h2, {
      id: "untyped-plutus-core",
      children: "Untyped Plutus Core"
    }), "\n", (0,jsx_runtime.jsx)(_components.p, {
      children: "Untyped Plutus Core (UPLC), also known simply as Plutus Core or Plutus, is a low-level, Turing-complete language based on untyped lambda calculus, a simple and well-established computational model that dates back to the 1930s.\nThanks to its simplicity and extensive academic research, the need for updates or modifications to the language over time is minimal, ensuring long-term stability.\nIt also facilitates the creation of simple, formally verified evaluators."
    }), "\n", (0,jsx_runtime.jsx)(_components.p, {
      children: "Along with UPLC and its evaluator, we provide a compiler from Plinth, a subset of Haskell, to UPLC.\nHowever, UPLC can be an easy compilation target for any language that supports functional-style programming, in particular immutable data and higher-order functions, both of which are widely adopted today in programming languages, and are particularly suited to Cardano's UTXO ledger model, where UTXOs are immutable."
    }), "\n", (0,jsx_runtime.jsx)(_components.p, {
      children: "UPLC is the code that runs on-chain, i.e., by every node validating the transaction, using an interpreter known as the CEK machine.\nA UPLC program included in a Cardano transaction is often referred to as a Plutus script or a Plutus validator."
    }), "\n", (0,jsx_runtime.jsx)(_components.h3, {
      id: "typed-plutus-core-and-plutus-ir",
      children: "Typed Plutus Core and Plutus IR"
    }), "\n", (0,jsx_runtime.jsx)(_components.p, {
      children: "Typed Plutus Core (TPLC) is the intrinsically typed counterpart of UPLC.\nIt is based on higher-order polymorphic lambda calculus with isorecursive types (System Fωμ).\nTPLC serves as a low-level intermediate representation (IR) for the Plinth compiler.\nTPLC is closely related to UPLC, and compiling TPLC into UPLC is simply a matter of erasing types."
    }), "\n", (0,jsx_runtime.jsx)(_components.p, {
      children: "Plutus IR (PIR) is a high-level IR also used by the Plinth compiler.\nIt extends TPLC by adding recursive bindings and recursive data types.\nThe fact that recursion is explicit in PIR, rather than encoded using fixed point operators as in TPLC and UPLC, makes PIR significantly more readable than TPLC and UPLC.\nWhen optimizing the cost or size of Plutus scripts written in Plinth, it is usually useful to look into PIR."
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