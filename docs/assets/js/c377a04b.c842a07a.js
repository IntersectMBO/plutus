"use strict";
(self["webpackChunkdocusaurus"] = self["webpackChunkdocusaurus"] || []).push([[3361],{

/***/ 3012:
/***/ ((__unused_webpack_module, __webpack_exports__, __webpack_require__) => {

// ESM COMPAT FLAG
__webpack_require__.r(__webpack_exports__);

// EXPORTS
__webpack_require__.d(__webpack_exports__, {
  assets: () => (/* binding */ assets),
  contentTitle: () => (/* binding */ contentTitle),
  "default": () => (/* binding */ MDXContent),
  frontMatter: () => (/* binding */ frontMatter),
  metadata: () => (/* reexport */ site_docs_index_md_c37_namespaceObject),
  toc: () => (/* binding */ toc)
});

;// ./.docusaurus/docusaurus-plugin-content-docs/default/site-docs-index-md-c37.json
const site_docs_index_md_c37_namespaceObject = /*#__PURE__*/JSON.parse('{"id":"index","title":"Plutus User Guide","description":"Welcome to the Plutus user guide.","source":"@site/docs/index.md","sourceDirName":".","slug":"/","permalink":"/docs/","draft":false,"unlisted":false,"editUrl":"https://github.com/IntersectMBO/plutus/edit/master/doc/docusaurus/docs/index.md","tags":[],"version":"current","sidebarPosition":0,"frontMatter":{"sidebar_position":0},"sidebar":"tutorialSidebar","next":{"title":"Example: An Auction Smart Contract","permalink":"/docs/category/example-an-auction-smart-contract"}}');
// EXTERNAL MODULE: ./node_modules/react/jsx-runtime.js
var jsx_runtime = __webpack_require__(4848);
// EXTERNAL MODULE: ./node_modules/@mdx-js/react/lib/index.js
var lib = __webpack_require__(8453);
;// ./docs/index.md


const frontMatter = {
	sidebar_position: 0
};
const contentTitle = 'Plutus User Guide';

const assets = {

};



const toc = [];
function _createMdxContent(props) {
  const _components = {
    a: "a",
    h1: "h1",
    header: "header",
    p: "p",
    ...(0,lib/* useMDXComponents */.R)(),
    ...props.components
  };
  return (0,jsx_runtime.jsxs)(jsx_runtime.Fragment, {
    children: [(0,jsx_runtime.jsx)(_components.header, {
      children: (0,jsx_runtime.jsx)(_components.h1, {
        id: "plutus-user-guide",
        children: "Plutus User Guide"
      })
    }), "\n", (0,jsx_runtime.jsx)(_components.p, {
      children: "Welcome to the Plutus user guide."
    }), "\n", (0,jsx_runtime.jsx)(_components.p, {
      children: "This guide focuses primarily on Plutus Tx, a subset of Haskell tailored for implementing smart contracts on Cardano.\nAs a subset of Haskell, Plutus Tx is high level and purely functional, and leverages Haskell's powerful type system.\nThis empowers developers to write secure, reliable and deterministic code, which is essential for smart contract development."
    }), "\n", (0,jsx_runtime.jsx)(_components.p, {
      children: "Plutus Tx is used to write on-chain code, often called scripts or validators.\nTo fully develop and deploy smart contracts, off-chain code is also needed for tasks such as building and submitting transactions, querying available UTXOs, and more.\nA detailed discussion of off-chain code is beyond the scope of this guide."
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["Besides Plutus Tx, this guide also covers other languages and components in the ", (0,jsx_runtime.jsx)(_components.a, {
        href: "https://github.com/IntersectMBO/plutus",
        children: "plutus repository"
      }), ", including Untyped Plutus Core, Typed Plutus Core, Plutus IR, evaluation and costing of programs, among other topics.\nWhile these subjects are not covered in depth, you can find links to specifications and papers for further reading in the ", (0,jsx_runtime.jsx)(_components.a, {
        href: "/docs/delve-deeper/further-resources",
        children: "Further Resources"
      }), " section.\nVisit the ", (0,jsx_runtime.jsx)(_components.a, {
        href: "/docs/glossary",
        children: "Glossary"
      }), " page for brief descriptions of these concepts."]
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