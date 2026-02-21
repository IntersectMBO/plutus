"use strict";
(self["webpackChunkdocusaurus"] = self["webpackChunkdocusaurus"] || []).push([[5207],{

/***/ 8235:
/***/ ((__unused_webpack_module, __webpack_exports__, __webpack_require__) => {

// ESM COMPAT FLAG
__webpack_require__.r(__webpack_exports__);

// EXPORTS
__webpack_require__.d(__webpack_exports__, {
  assets: () => (/* binding */ assets),
  contentTitle: () => (/* binding */ contentTitle),
  "default": () => (/* binding */ MDXContent),
  frontMatter: () => (/* binding */ frontMatter),
  metadata: () => (/* reexport */ site_docs_auction_smart_contract_end_to_end_getting_funds_md_97c_namespaceObject),
  toc: () => (/* binding */ toc)
});

;// ./.docusaurus/docusaurus-plugin-content-docs/default/site-docs-auction-smart-contract-end-to-end-getting-funds-md-97c.json
const site_docs_auction_smart_contract_end_to_end_getting_funds_md_97c_namespaceObject = /*#__PURE__*/JSON.parse('{"id":"auction-smart-contract/end-to-end/getting-funds","title":"Getting Funds from the Faucet","description":"Next, we\'ll need to fund the wallet of each participant (seller, bidder1 and bidder2), in order to cover transaction fees and place bids.","source":"@site/docs/auction-smart-contract/end-to-end/getting-funds.md","sourceDirName":"auction-smart-contract/end-to-end","slug":"/auction-smart-contract/end-to-end/getting-funds","permalink":"/pr-preview/docs/pr-7516/auction-smart-contract/end-to-end/getting-funds","draft":false,"unlisted":false,"editUrl":"https://github.com/IntersectMBO/plutus/edit/master/doc/docusaurus/docs/auction-smart-contract/end-to-end/getting-funds.md","tags":[],"version":"current","sidebarPosition":10,"frontMatter":{"sidebar_position":10},"sidebar":"tutorialSidebar","previous":{"title":"Generating Keys and Addresses","permalink":"/pr-preview/docs/pr-7516/auction-smart-contract/end-to-end/generating-keys"},"next":{"title":"Minting the Token to be Auctioned","permalink":"/pr-preview/docs/pr-7516/auction-smart-contract/end-to-end/mint"}}');
// EXTERNAL MODULE: ./node_modules/react/jsx-runtime.js
var jsx_runtime = __webpack_require__(4848);
// EXTERNAL MODULE: ./node_modules/@mdx-js/react/lib/index.js
var lib = __webpack_require__(8453);
;// ./docs/auction-smart-contract/end-to-end/getting-funds.md


const frontMatter = {
	sidebar_position: 10
};
const contentTitle = 'Getting Funds from the Faucet';

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
    pre: "pre",
    ...(0,lib/* useMDXComponents */.R)(),
    ...props.components
  }, {LiteralInclude} = _components;
  if (!LiteralInclude) _missingMdxReference("LiteralInclude", true);
  return (0,jsx_runtime.jsxs)(jsx_runtime.Fragment, {
    children: [(0,jsx_runtime.jsx)(_components.header, {
      children: (0,jsx_runtime.jsx)(_components.h1, {
        id: "getting-funds-from-the-faucet",
        children: "Getting Funds from the Faucet"
      })
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["Next, we'll need to fund the wallet of each participant (seller, bidder1 and bidder2), in order to cover transaction fees and place bids.\nWe can get funds from Cardano's ", (0,jsx_runtime.jsx)(_components.a, {
        href: "https://docs.cardano.org/cardano-testnets/tools/faucet/",
        children: "testnet faucet"
      }), "."]
    }), "\n", (0,jsx_runtime.jsx)(_components.p, {
      children: "To request funds, enter the seller's address into the address field and click \"request funds.\"\nThis will deposit 10,000 (test) ADA into the seller's wallet.\nMake sure you select the correct network (Preview)."
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["Since the faucet limits how frequently you can request funds, and 10,000 ADA is more than sufficient for this example, we'll share the 10,000 ADA among the seller, bidder1, and bidder2.\nTo do so, create a file named ", (0,jsx_runtime.jsx)(_components.code, {
        children: "off-chain/send-lovelace.mjs"
      }), " with the following content:"]
    }), "\n", (0,jsx_runtime.jsx)(LiteralInclude, {
      file: "send-lovelace.mjs",
      language: "javascript",
      title: "send-lovelace.mjs"
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["Substitute your Blockfrost project ID for ", (0,jsx_runtime.jsx)(_components.code, {
        children: "Replace with Blockfrost Project ID"
      }), "."]
    }), "\n", (0,jsx_runtime.jsx)(_components.p, {
      children: "This Javascript module builds and submits a transaction that sends 1 billion Lovelace (equivalent to 1000 Ada) from the seller's wallet to the specified recipient.\nRun the following commands:"
    }), "\n", (0,jsx_runtime.jsx)(_components.pre, {
      children: (0,jsx_runtime.jsx)(_components.code, {
        children: "node send-lovelace.mjs bidder1\nnode send-lovelace.mjs bidder2\n"
      })
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["After the transactions are confirmed and included in a block (usually within a minute), bidder1's and bidder2's wallets should each have 1000 Ada, and the seller's wallet should have approximately 8000 Ada (minus transaction fees), which you can verify on ", (0,jsx_runtime.jsx)(_components.a, {
        href: "https://preview.cardanoscan.io/",
        children: "Cardanoscan"
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
function _missingMdxReference(id, component) {
  throw new Error("Expected " + (component ? "component" : "object") + " `" + id + "` to be defined: you likely forgot to import, pass, or provide it.");
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