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
const site_docs_index_md_c37_namespaceObject = /*#__PURE__*/JSON.parse('{"id":"index","title":"Plinth User Guide","description":"Welcome to the Plinth user guide.","source":"@site/docs/index.md","sourceDirName":".","slug":"/","permalink":"/pr-preview/docs/pr-7364/","draft":false,"unlisted":false,"editUrl":"https://github.com/IntersectMBO/plutus/edit/master/doc/docusaurus/docs/index.md","tags":[],"version":"current","sidebarPosition":0,"frontMatter":{"sidebar_position":0},"sidebar":"tutorialSidebar","next":{"title":"Essential concepts","permalink":"/pr-preview/docs/pr-7364/category/essential-concepts"}}');
// EXTERNAL MODULE: ./node_modules/react/jsx-runtime.js
var jsx_runtime = __webpack_require__(4848);
// EXTERNAL MODULE: ./node_modules/@mdx-js/react/lib/index.js
var lib = __webpack_require__(8453);
;// ./docs/index.md


const frontMatter = {
	sidebar_position: 0
};
const contentTitle = 'Plinth User Guide';

const assets = {

};



const toc = [];
function _createMdxContent(props) {
  const _components = {
    a: "a",
    h1: "h1",
    header: "header",
    p: "p",
    strong: "strong",
    ...(0,lib/* useMDXComponents */.R)(),
    ...props.components
  };
  return (0,jsx_runtime.jsxs)(jsx_runtime.Fragment, {
    children: [(0,jsx_runtime.jsx)(_components.header, {
      children: (0,jsx_runtime.jsx)(_components.h1, {
        id: "plinth-user-guide",
        children: "Plinth User Guide"
      })
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["Welcome to the Plinth user guide.\nThis guide covers ", (0,jsx_runtime.jsx)(_components.strong, {
        children: "Plinth"
      }), " (formerly Plutus Tx), a subset of Haskell tailored for implementing smart contracts on Cardano, and its compilation target, ", (0,jsx_runtime.jsx)(_components.strong, {
        children: "Plutus Core"
      }), ", a low level lambda calculus based language for on-chain execution."]
    }), "\n", (0,jsx_runtime.jsx)(_components.p, {
      children: "As a subset of Haskell, Plinth is high level and purely functional, and leverages Haskell's powerful type system.\nThis empowers developers to write secure, reliable and deterministic code, which is essential for smart contract development."
    }), "\n", (0,jsx_runtime.jsx)(_components.p, {
      children: "Plinth is used to write on-chain code, often called scripts or validators.\nTo fully develop and deploy smart contracts, off-chain code is also needed for tasks such as building and submitting transactions, querying available UTXOs, and more.\nA detailed discussion of off-chain code is beyond the scope of this guide."
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["While not all subjects are not covered in depth, you can find links to specifications and papers for further reading in the ", (0,jsx_runtime.jsx)(_components.a, {
        href: "category/further-resources",
        children: "Further Resources"
      }), " section.\nVisit the ", (0,jsx_runtime.jsx)(_components.a, {
        href: "/pr-preview/docs/pr-7364/glossary",
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