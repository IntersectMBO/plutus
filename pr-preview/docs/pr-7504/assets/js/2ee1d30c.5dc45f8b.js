"use strict";
(self["webpackChunkdocusaurus"] = self["webpackChunkdocusaurus"] || []).push([[7506],{

/***/ 1977:
/***/ ((__unused_webpack_module, __webpack_exports__, __webpack_require__) => {

// ESM COMPAT FLAG
__webpack_require__.r(__webpack_exports__);

// EXPORTS
__webpack_require__.d(__webpack_exports__, {
  assets: () => (/* binding */ assets),
  contentTitle: () => (/* binding */ contentTitle),
  "default": () => (/* binding */ MDXContent),
  frontMatter: () => (/* binding */ frontMatter),
  metadata: () => (/* reexport */ site_docs_delve_deeper_understanding_script_hashes_md_2ee_namespaceObject),
  toc: () => (/* binding */ toc)
});

;// ./.docusaurus/docusaurus-plugin-content-docs/default/site-docs-delve-deeper-understanding-script-hashes-md-2ee.json
const site_docs_delve_deeper_understanding_script_hashes_md_2ee_namespaceObject = /*#__PURE__*/JSON.parse('{"id":"delve-deeper/understanding-script-hashes","title":"Understanding Script Hashes","description":"Script hashes are a core concept and play a vital role on Cardano.","source":"@site/docs/delve-deeper/understanding-script-hashes.md","sourceDirName":"delve-deeper","slug":"/delve-deeper/understanding-script-hashes","permalink":"/pr-preview/docs/pr-7504/delve-deeper/understanding-script-hashes","draft":false,"unlisted":false,"editUrl":"https://github.com/IntersectMBO/plutus/edit/master/doc/docusaurus/docs/delve-deeper/understanding-script-hashes.md","tags":[],"version":"current","sidebarPosition":20,"frontMatter":{"sidebar_position":20},"sidebar":"tutorialSidebar","previous":{"title":"Cost Model","permalink":"/pr-preview/docs/pr-7504/delve-deeper/cost-model"},"next":{"title":"Encoding Data Types in UPLC","permalink":"/pr-preview/docs/pr-7504/delve-deeper/encoding"}}');
// EXTERNAL MODULE: ./node_modules/react/jsx-runtime.js
var jsx_runtime = __webpack_require__(4848);
// EXTERNAL MODULE: ./node_modules/@mdx-js/react/lib/index.js
var lib = __webpack_require__(8453);
;// ./docs/delve-deeper/understanding-script-hashes.md


const frontMatter = {
	sidebar_position: 20
};
const contentTitle = 'Understanding Script Hashes';

const assets = {

};



const toc = [{
  "value": "Changing ledger language versions leads to changed script hashes",
  "id": "changing-ledger-language-versions-leads-to-changed-script-hashes",
  "level": 2
}, {
  "value": "Changing Plinth compiler versions may lead to changed script hashes",
  "id": "changing-plinth-compiler-versions-may-lead-to-changed-script-hashes",
  "level": 2
}];
function _createMdxContent(props) {
  const _components = {
    a: "a",
    h1: "h1",
    h2: "h2",
    header: "header",
    p: "p",
    ...(0,lib/* useMDXComponents */.R)(),
    ...props.components
  };
  return (0,jsx_runtime.jsxs)(jsx_runtime.Fragment, {
    children: [(0,jsx_runtime.jsx)(_components.header, {
      children: (0,jsx_runtime.jsx)(_components.h1, {
        id: "understanding-script-hashes",
        children: "Understanding Script Hashes"
      })
    }), "\n", (0,jsx_runtime.jsx)(_components.p, {
      children: "Script hashes are a core concept and play a vital role on Cardano.\nPerforming an action on Cardano that involves scripts, such as spending a script UTXO or minting tokens, requires the script with a specific hash to be executed and satisfied.\nThe cryptographic security of script hashes makes it effectively impossible to manufacture a script that matches a given hash, ensuring the integrity of the blockchain.\nA solid understanding of script hashes is essential for DApp development."
    }), "\n", (0,jsx_runtime.jsx)(_components.h2, {
      id: "changing-ledger-language-versions-leads-to-changed-script-hashes",
      children: "Changing ledger language versions leads to changed script hashes"
    }), "\n", (0,jsx_runtime.jsx)(_components.p, {
      children: "The ledger language version of a script is part of its hash, so the exact same UPLC program will have different hashes when used as a Plutus V1, V2 or V3 script.\nThis means, for example, you can't supply a Plutus V3 script when performing an action that requires a Plutus V1 or V2 script, as the hash won't match."
    }), "\n", (0,jsx_runtime.jsx)(_components.h2, {
      id: "changing-plinth-compiler-versions-may-lead-to-changed-script-hashes",
      children: "Changing Plinth compiler versions may lead to changed script hashes"
    }), "\n", (0,jsx_runtime.jsx)(_components.p, {
      children: "Different Plinth compiler versions may compile and optimize the same Plinth code differently, leading to different UPLC programs and, therefore, different script hashes."
    }), "\n", (0,jsx_runtime.jsx)(_components.p, {
      children: "Additionally, the version of GHC can affect the resulting UPLC program and script hashes.\nWhile the Plinth compiler currently supports only one major GHC version, different minor GHC versions may lead to slightly different UPLC programs."
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["If you plan to use your script in the future, the best approach is to save the compiled script in a blueprint file.\nFor further information, refer to ", (0,jsx_runtime.jsx)(_components.a, {
        href: "/pr-preview/docs/pr-7504/working-with-scripts/producing-a-blueprint",
        children: "Producing a Plutus contract blueprint"
      }), "."]
    }), "\n", (0,jsx_runtime.jsx)(_components.p, {
      children: "If you wish to compile your Plinth code again in the future while ensuring the script hash remains unchanged, consider using Nix to lock the versions of all dependencies by pinning to a specific version of nixpkgs."
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