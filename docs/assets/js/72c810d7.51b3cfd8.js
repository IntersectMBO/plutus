"use strict";
(self["webpackChunkdocusaurus"] = self["webpackChunkdocusaurus"] || []).push([[1041],{

/***/ 2932:
/***/ ((__unused_webpack_module, __webpack_exports__, __webpack_require__) => {

// ESM COMPAT FLAG
__webpack_require__.r(__webpack_exports__);

// EXPORTS
__webpack_require__.d(__webpack_exports__, {
  assets: () => (/* binding */ assets),
  contentTitle: () => (/* binding */ contentTitle),
  "default": () => (/* binding */ MDXContent),
  frontMatter: () => (/* binding */ frontMatter),
  metadata: () => (/* reexport */ site_docs_using_plutus_tx_environment_setup_md_72c_namespaceObject),
  toc: () => (/* binding */ toc)
});

;// ./.docusaurus/docusaurus-plugin-content-docs/default/site-docs-using-plutus-tx-environment-setup-md-72c.json
const site_docs_using_plutus_tx_environment_setup_md_72c_namespaceObject = /*#__PURE__*/JSON.parse('{"id":"using-plutus-tx/environment-setup","title":"Environment Setup","description":"Plutus Tx is a subset of Haskell, so configuring the development environment for Plutus Tx is similar to a regular Haskell environment setup.","source":"@site/docs/using-plutus-tx/environment-setup.md","sourceDirName":"using-plutus-tx","slug":"/using-plutus-tx/environment-setup","permalink":"/docs/using-plutus-tx/environment-setup","draft":false,"unlisted":false,"editUrl":"https://github.com/IntersectMBO/plutus/edit/master/doc/docusaurus/docs/using-plutus-tx/environment-setup.md","tags":[],"version":"current","sidebarPosition":5,"frontMatter":{"sidebar_position":5},"sidebar":"tutorialSidebar","previous":{"title":"Using Plutus Tx","permalink":"/docs/category/using-plutus-tx"},"next":{"title":"Compiling Plutus Tx","permalink":"/docs/using-plutus-tx/compiling-plutus-tx"}}');
// EXTERNAL MODULE: ./node_modules/react/jsx-runtime.js
var jsx_runtime = __webpack_require__(4848);
// EXTERNAL MODULE: ./node_modules/@mdx-js/react/lib/index.js
var lib = __webpack_require__(8453);
;// ./docs/using-plutus-tx/environment-setup.md


const frontMatter = {
	sidebar_position: 5
};
const contentTitle = 'Environment Setup';

const assets = {

};



const toc = [];
function _createMdxContent(props) {
  const _components = {
    a: "a",
    code: "code",
    h1: "h1",
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
        id: "environment-setup",
        children: "Environment Setup"
      })
    }), "\n", (0,jsx_runtime.jsx)(_components.p, {
      children: "Plutus Tx is a subset of Haskell, so configuring the development environment for Plutus Tx is similar to a regular Haskell environment setup.\nHowever, there are a few additional requirements:"
    }), "\n", (0,jsx_runtime.jsxs)(_components.ul, {
      children: ["\n", (0,jsx_runtime.jsx)(_components.li, {
        children: "Plutus Tx supports a specific major version of GHC (currently 9.6)."
      }), "\n", (0,jsx_runtime.jsxs)(_components.li, {
        children: ["You’ll need some specific packages, such as ", (0,jsx_runtime.jsx)(_components.code, {
          children: "plutus-tx"
        }), " and ", (0,jsx_runtime.jsx)(_components.code, {
          children: "plutus-tx-plugin"
        }), ", which are hosted on the ", (0,jsx_runtime.jsx)(_components.a, {
          href: "https://github.com/IntersectMBO/cardano-haskell-packages",
          children: "Cardano Haskell Package repository"
        }), " (CHaP), rather than Hackage, Haskell's default package archive."]
      }), "\n", (0,jsx_runtime.jsxs)(_components.li, {
        children: ["You'll also need a few C libraries such as ", (0,jsx_runtime.jsx)(_components.code, {
          children: "secp256k1"
        }), " and ", (0,jsx_runtime.jsx)(_components.code, {
          children: "blst"
        }), ", which are required by the ", (0,jsx_runtime.jsx)(_components.code, {
          children: "plutus-tx"
        }), " library."]
      }), "\n"]
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["You can take care of all of the above requirements manually, but the recommended method is to use the Nix develop shell provided by the ", (0,jsx_runtime.jsx)(_components.a, {
        href: "https://github.com/IntersectMBO/plutus-tx-template",
        children: "plutus-tx-template repository"
      }), ".\nYou can clone the repository and run ", (0,jsx_runtime.jsx)(_components.code, {
        children: "nix develop"
      }), ".\nThe repository also includes a sample Cabal project, pre-configured to follow the Auction example, which you can immediately modify and explore."]
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["Alternatively, you can bypass cloning by running ", (0,jsx_runtime.jsx)(_components.code, {
        children: "nix develop github:IntersectMBO/plutus-tx-template"
      }), ".\nFor instructions on installing Nix, visit ", (0,jsx_runtime.jsx)(_components.a, {
        href: "https://nixos.org/download/",
        children: "nixos.org"
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