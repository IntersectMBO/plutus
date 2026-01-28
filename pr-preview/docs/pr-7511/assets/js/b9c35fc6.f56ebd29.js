"use strict";
(self["webpackChunkdocusaurus"] = self["webpackChunkdocusaurus"] || []).push([[7960],{

/***/ 6103:
/***/ ((__unused_webpack_module, __webpack_exports__, __webpack_require__) => {

// ESM COMPAT FLAG
__webpack_require__.r(__webpack_exports__);

// EXPORTS
__webpack_require__.d(__webpack_exports__, {
  assets: () => (/* binding */ assets),
  contentTitle: () => (/* binding */ contentTitle),
  "default": () => (/* binding */ MDXContent),
  frontMatter: () => (/* binding */ frontMatter),
  metadata: () => (/* reexport */ site_docs_haddock_documentation_md_b9c_namespaceObject),
  toc: () => (/* binding */ toc)
});

;// ./.docusaurus/docusaurus-plugin-content-docs/default/site-docs-haddock-documentation-md-b9c.json
const site_docs_haddock_documentation_md_b9c_namespaceObject = /*#__PURE__*/JSON.parse('{"id":"haddock-documentation","title":"Haddock Documentation","description":"Haddock is a tool for automatically generating documentation from annotated Haskell source code.","source":"@site/docs/haddock-documentation.md","sourceDirName":".","slug":"/haddock-documentation","permalink":"/pr-preview/docs/pr-7511/haddock-documentation","draft":false,"unlisted":false,"editUrl":"https://github.com/IntersectMBO/plutus/edit/master/doc/docusaurus/docs/haddock-documentation.md","tags":[],"version":"current","sidebarPosition":30,"frontMatter":{"sidebar_position":30},"sidebar":"tutorialSidebar","previous":{"title":"Glossary","permalink":"/pr-preview/docs/pr-7511/glossary"},"next":{"title":"Using Plinth","permalink":"/pr-preview/docs/pr-7511/category/using-plinth"}}');
// EXTERNAL MODULE: ./node_modules/react/jsx-runtime.js
var jsx_runtime = __webpack_require__(4848);
// EXTERNAL MODULE: ./node_modules/@mdx-js/react/lib/index.js
var lib = __webpack_require__(8453);
;// ./docs/haddock-documentation.md


const frontMatter = {
	sidebar_position: 30
};
const contentTitle = 'Haddock Documentation';

const assets = {

};



const toc = [];
function _createMdxContent(props) {
  const _components = {
    a: "a",
    code: "code",
    h1: "h1",
    header: "header",
    p: "p",
    ...(0,lib/* useMDXComponents */.R)(),
    ...props.components
  };
  return (0,jsx_runtime.jsxs)(jsx_runtime.Fragment, {
    children: [(0,jsx_runtime.jsx)(_components.header, {
      children: (0,jsx_runtime.jsx)(_components.h1, {
        id: "haddock-documentation",
        children: "Haddock Documentation"
      })
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["Haddock is a tool for automatically generating documentation from annotated Haskell source code.\nThe Haddock for the latest release of public libraries from the ", (0,jsx_runtime.jsx)(_components.a, {
        href: "https://github.com/IntersectMBO/plutus",
        children: "plutus repository"
      }), " is available ", (0,jsx_runtime.jsx)(_components.a, {
        href: "https://plutus.cardano.intersectmbo.org/haddock/latest",
        children: "here"
      }), ".\nYou can also use the dropdown menu to view the Haddock for an older release or the master branch."]
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["If you are writing scripts with Plinth, start from ", (0,jsx_runtime.jsx)(_components.a, {
        href: "https://plutus.cardano.intersectmbo.org/haddock/latest/plutus-tx/PlutusTx.html",
        children: (0,jsx_runtime.jsx)(_components.code, {
          children: "Plutus.Tx"
        })
      }), " and ", (0,jsx_runtime.jsx)(_components.a, {
        href: "https://plutus.cardano.intersectmbo.org/haddock/latest/plutus-tx/PlutusTx-Prelude.html",
        children: (0,jsx_runtime.jsx)(_components.code, {
          children: "PlutusTx.Prelude"
        })
      }), "."]
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["If you're interested in learning about lower-level languages, check out ", (0,jsx_runtime.jsx)(_components.a, {
        href: "https://plutus.cardano.intersectmbo.org/haddock/latest/plutus-core/PlutusCore.html",
        children: (0,jsx_runtime.jsx)(_components.code, {
          children: "PlutusCore"
        })
      }), " and ", (0,jsx_runtime.jsx)(_components.a, {
        href: "https://plutus.cardano.intersectmbo.org/haddock/latest/plutus-core/UntypedPlutusCore.html",
        children: (0,jsx_runtime.jsx)(_components.code, {
          children: "UntypedPlutusCore"
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