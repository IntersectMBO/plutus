"use strict";
(self["webpackChunkdocusaurus"] = self["webpackChunkdocusaurus"] || []).push([[507],{

/***/ 1178:
/***/ ((__unused_webpack_module, __webpack_exports__, __webpack_require__) => {

// ESM COMPAT FLAG
__webpack_require__.r(__webpack_exports__);

// EXPORTS
__webpack_require__.d(__webpack_exports__, {
  assets: () => (/* binding */ assets),
  contentTitle: () => (/* binding */ contentTitle),
  "default": () => (/* binding */ MDXContent),
  frontMatter: () => (/* binding */ frontMatter),
  metadata: () => (/* reexport */ site_docs_auction_smart_contract_end_to_end_generating_keys_md_51f_namespaceObject),
  toc: () => (/* binding */ toc)
});

;// ./.docusaurus/docusaurus-plugin-content-docs/default/site-docs-auction-smart-contract-end-to-end-generating-keys-md-51f.json
const site_docs_auction_smart_contract_end_to_end_generating_keys_md_51f_namespaceObject = /*#__PURE__*/JSON.parse('{"id":"auction-smart-contract/end-to-end/generating-keys","title":"Generating Keys and Addresses","description":"The best way to setup your environment is with the plinth-template repository. See its README for complete instructions on how to get up and running using Docker, Nix, or a custom approach.","source":"@site/docs/auction-smart-contract/end-to-end/generating-keys.md","sourceDirName":"auction-smart-contract/end-to-end","slug":"/auction-smart-contract/end-to-end/generating-keys","permalink":"/pr-preview/docs/pr-7544/auction-smart-contract/end-to-end/generating-keys","draft":false,"unlisted":false,"editUrl":"https://github.com/IntersectMBO/plutus/edit/master/doc/docusaurus/docs/auction-smart-contract/end-to-end/generating-keys.md","tags":[],"version":"current","sidebarPosition":5,"frontMatter":{"sidebar_position":5},"sidebar":"tutorialSidebar","previous":{"title":"End to end","permalink":"/pr-preview/docs/pr-7544/category/end-to-end"},"next":{"title":"Getting Funds from the Faucet","permalink":"/pr-preview/docs/pr-7544/auction-smart-contract/end-to-end/getting-funds"}}');
// EXTERNAL MODULE: ./node_modules/react/jsx-runtime.js
var jsx_runtime = __webpack_require__(4848);
// EXTERNAL MODULE: ./node_modules/@mdx-js/react/lib/index.js
var lib = __webpack_require__(8453);
;// ./docs/auction-smart-contract/end-to-end/generating-keys.md


const frontMatter = {
	sidebar_position: 5
};
const contentTitle = 'Generating Keys and Addresses';

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
        id: "generating-keys-and-addresses",
        children: "Generating Keys and Addresses"
      })
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["The best way to setup your environment is with the ", (0,jsx_runtime.jsx)(_components.a, {
        href: "https://github.com/IntersectMBO/plinth-template",
        children: "plinth-template"
      }), " repository. See its ", (0,jsx_runtime.jsx)(_components.a, {
        href: "https://github.com/IntersectMBO/plinth-template?tab=readme-ov-file#plinth-template",
        children: "README"
      }), " for complete instructions on how to get up and running using Docker, Nix, or a custom approach."]
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["Make sure you also have ", (0,jsx_runtime.jsx)(_components.a, {
        href: "https://nodejs.org/en",
        children: "NodeJS"
      }), " and ", (0,jsx_runtime.jsx)(_components.a, {
        href: "https://yarnpkg.com/",
        children: "yarn"
      }), " (or ", (0,jsx_runtime.jsx)(_components.a, {
        href: "https://github.com/npm/cli",
        children: "npm"
      }), ", which comes with ", (0,jsx_runtime.jsx)(_components.code, {
        children: "NodeJS"
      }), ") installed.\nThen, create a separate ", (0,jsx_runtime.jsx)(_components.code, {
        children: "off-chain"
      }), " directory, initialize ", (0,jsx_runtime.jsx)(_components.code, {
        children: "package.json"
      }), ", and install the required dependencies:"]
    }), "\n", (0,jsx_runtime.jsx)(_components.pre, {
      children: (0,jsx_runtime.jsx)(_components.code, {
        children: "git clone git@github.com:IntersectMBO/plinth-template.git on-chain\nmkdir off-chain && cd $_\nyarn init -y\nyarn add @meshsdk/core\nyarn add @harmoniclabs/pair\nyarn add cbor\n"
      })
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["We'll use ", (0,jsx_runtime.jsx)(_components.a, {
        href: "https://meshjs.dev/",
        children: "mesh"
      }), ", a JavaScript framework, for writing off-chain code.\nWe'll use ", (0,jsx_runtime.jsx)(_components.a, {
        href: "https://blockfrost.io/",
        children: "Blockfrost"
      }), " as the blockchain provider, to avoid the need of running a local node.\nIf you don't have a Blockfrost account, you can sign up for one, and create a project for the Preview network."]
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["The first step is to generate keys and addresses for the seller and the bidders.\nAdd a new file named ", (0,jsx_runtime.jsx)(_components.code, {
        children: "off-chain/generate-keys.mjs"
      }), ", with the following content:"]
    }), "\n", (0,jsx_runtime.jsx)(LiteralInclude, {
      file: "generate-keys.mjs",
      language: "javascript",
      title: "generate-keys.mjs"
    }), "\n", (0,jsx_runtime.jsx)(_components.p, {
      children: "Then, generate keys and addresses for one seller and two bidders by running:"
    }), "\n", (0,jsx_runtime.jsx)(_components.pre, {
      children: (0,jsx_runtime.jsx)(_components.code, {
        children: "node generate-keys.mjs seller\nnode generate-keys.mjs bidder1\nnode generate-keys.mjs bidder2\n"
      })
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["This will create three files for each participant (seller, bidder1, and bidder2): a ", (0,jsx_runtime.jsx)(_components.code, {
        children: ".skey"
      }), " file that contains a secret key, a ", (0,jsx_runtime.jsx)(_components.code, {
        children: ".addr"
      }), " file that contains the corresponding wallet address, and a ", (0,jsx_runtime.jsx)(_components.code, {
        children: ".pkh"
      }), " file that contains the corresponding public key hash."]
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