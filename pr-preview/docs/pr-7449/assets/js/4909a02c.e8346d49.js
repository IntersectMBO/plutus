"use strict";
(self["webpackChunkdocusaurus"] = self["webpackChunkdocusaurus"] || []).push([[4325],{

/***/ 1131:
/***/ ((__unused_webpack_module, __webpack_exports__, __webpack_require__) => {

// ESM COMPAT FLAG
__webpack_require__.r(__webpack_exports__);

// EXPORTS
__webpack_require__.d(__webpack_exports__, {
  assets: () => (/* binding */ assets),
  contentTitle: () => (/* binding */ contentTitle),
  "default": () => (/* binding */ MDXContent),
  frontMatter: () => (/* binding */ frontMatter),
  metadata: () => (/* reexport */ site_docs_delve_deeper_further_resources_plutus_core_specification_md_490_namespaceObject),
  toc: () => (/* binding */ toc)
});

;// ./.docusaurus/docusaurus-plugin-content-docs/default/site-docs-delve-deeper-further-resources-plutus-core-specification-md-490.json
const site_docs_delve_deeper_further_resources_plutus_core_specification_md_490_namespaceObject = /*#__PURE__*/JSON.parse('{"id":"delve-deeper/further-resources/plutus-core-specification","title":"Plutus Core Specification","description":"The formal specification provides a comprehensive mathematical foundation for understanding the semantics and behavior of Plutus smart contracts.","source":"@site/docs/delve-deeper/further-resources/plutus-core-specification.md","sourceDirName":"delve-deeper/further-resources","slug":"/delve-deeper/further-resources/plutus-core-specification","permalink":"/pr-preview/docs/pr-7449/delve-deeper/further-resources/plutus-core-specification","draft":false,"unlisted":false,"editUrl":"https://github.com/IntersectMBO/plutus/edit/master/doc/docusaurus/docs/delve-deeper/further-resources/plutus-core-specification.md","tags":[],"version":"current","sidebarPosition":10,"frontMatter":{"sidebar_position":10},"sidebar":"tutorialSidebar","previous":{"title":"Publications","permalink":"/pr-preview/docs/pr-7449/delve-deeper/further-resources/publications"},"next":{"title":"Plutus-Related CIPs","permalink":"/pr-preview/docs/pr-7449/delve-deeper/further-resources/plutus-cips"}}');
// EXTERNAL MODULE: ./node_modules/react/jsx-runtime.js
var jsx_runtime = __webpack_require__(4848);
// EXTERNAL MODULE: ./node_modules/@mdx-js/react/lib/index.js
var lib = __webpack_require__(8453);
;// ./docs/delve-deeper/further-resources/plutus-core-specification.md


const frontMatter = {
	sidebar_position: 10
};
const contentTitle = 'Plutus Core Specification';

const assets = {

};



const toc = [];
function _createMdxContent(props) {
  const _components = {
    a: "a",
    h1: "h1",
    header: "header",
    li: "li",
    p: "p",
    strong: "strong",
    ul: "ul",
    ...(0,lib/* useMDXComponents */.R)(),
    ...props.components
  };
  return (0,jsx_runtime.jsxs)(jsx_runtime.Fragment, {
    children: [(0,jsx_runtime.jsx)(_components.header, {
      children: (0,jsx_runtime.jsx)(_components.h1, {
        id: "plutus-core-specification",
        children: "Plutus Core Specification"
      })
    }), "\n", (0,jsx_runtime.jsx)(_components.p, {
      children: "The formal specification provides a comprehensive mathematical foundation for understanding the semantics and behavior of Plutus smart contracts."
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["📄 ", (0,jsx_runtime.jsx)(_components.strong, {
        children: (0,jsx_runtime.jsx)(_components.a, {
          href: "https://plutus.cardano.intersectmbo.org/resources/plutus-core-spec.pdf",
          children: "Formal Specification of the Plutus Core Language"
        })
      })]
    }), "\n", (0,jsx_runtime.jsx)(_components.p, {
      children: "This specification is periodically updated to reflect changes and improvements to the language and its cost model."
    }), "\n", (0,jsx_runtime.jsx)(_components.p, {
      children: "This specification document includes:"
    }), "\n", (0,jsx_runtime.jsxs)(_components.ul, {
      children: ["\n", (0,jsx_runtime.jsxs)(_components.li, {
        children: [(0,jsx_runtime.jsx)(_components.strong, {
          children: "Syntax and Semantics"
        }), ": Complete formal definition of the Plutus Core language syntax and operational semantics"]
      }), "\n", (0,jsx_runtime.jsxs)(_components.li, {
        children: [(0,jsx_runtime.jsx)(_components.strong, {
          children: "Type System"
        }), ": Detailed description of the type system and typing rules"]
      }), "\n", (0,jsx_runtime.jsxs)(_components.li, {
        children: [(0,jsx_runtime.jsx)(_components.strong, {
          children: "Evaluation Rules"
        }), ": Precise specification of how Plutus Core programs are evaluated"]
      }), "\n", (0,jsx_runtime.jsxs)(_components.li, {
        children: [(0,jsx_runtime.jsx)(_components.strong, {
          children: "Builtin Functions"
        }), ": Formal treatment of builtin functions and their semantics"]
      }), "\n", (0,jsx_runtime.jsxs)(_components.li, {
        children: [(0,jsx_runtime.jsx)(_components.strong, {
          children: "Cost Model"
        }), ": Mathematical framework for the cost model used in script execution"]
      }), "\n"]
    }), "\n", (0,jsx_runtime.jsx)(_components.p, {
      children: "The formal specification serves as the authoritative reference for:"
    }), "\n", (0,jsx_runtime.jsxs)(_components.ul, {
      children: ["\n", (0,jsx_runtime.jsx)(_components.li, {
        children: "Compiler developers implementing Plutus Core"
      }), "\n", (0,jsx_runtime.jsx)(_components.li, {
        children: "Researchers studying the theoretical properties of the language"
      }), "\n", (0,jsx_runtime.jsx)(_components.li, {
        children: "Developers seeking deep understanding of script execution mechanics"
      }), "\n", (0,jsx_runtime.jsx)(_components.li, {
        children: "Auditors verifying the correctness of smart contract implementations"
      }), "\n"]
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