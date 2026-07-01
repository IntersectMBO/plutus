"use strict";
(self["webpackChunkdocusaurus"] = self["webpackChunkdocusaurus"] || []).push([[7587],{

/***/ 8704:
/***/ ((__unused_webpack_module, __webpack_exports__, __webpack_require__) => {

// ESM COMPAT FLAG
__webpack_require__.r(__webpack_exports__);

// EXPORTS
__webpack_require__.d(__webpack_exports__, {
  assets: () => (/* binding */ assets),
  contentTitle: () => (/* binding */ contentTitle),
  "default": () => (/* binding */ MDXContent),
  frontMatter: () => (/* binding */ frontMatter),
  metadata: () => (/* reexport */ site_docs_essential_concepts_versions_md_0c1_namespaceObject),
  toc: () => (/* binding */ toc)
});

;// ./.docusaurus/docusaurus-plugin-content-docs/default/site-docs-essential-concepts-versions-md-0c1.json
const site_docs_essential_concepts_versions_md_0c1_namespaceObject = /*#__PURE__*/JSON.parse('{"id":"essential-concepts/versions","title":"Different Notions of Version","description":"There are several different notions of version that Cardano smart contract developers must distinguish.","source":"@site/docs/essential-concepts/versions.md","sourceDirName":"essential-concepts","slug":"/essential-concepts/versions","permalink":"/pr-preview/pr-7352/essential-concepts/versions","draft":false,"unlisted":false,"editUrl":"https://github.com/IntersectMBO/plutus/edit/master/doc/docusaurus/docs/essential-concepts/versions.md","tags":[],"version":"current","sidebarPosition":10,"frontMatter":{"sidebar_position":10},"sidebar":"tutorialSidebar","previous":{"title":"Plinth and Plutus Core","permalink":"/pr-preview/pr-7352/essential-concepts/plinth-and-plutus-core"},"next":{"title":"Scripts and the Extended UTXO Model","permalink":"/pr-preview/pr-7352/essential-concepts/eutxo"}}');
// EXTERNAL MODULE: ./node_modules/react/jsx-runtime.js
var jsx_runtime = __webpack_require__(4848);
// EXTERNAL MODULE: ./node_modules/@mdx-js/react/lib/index.js
var lib = __webpack_require__(8453);
;// ./docs/essential-concepts/versions.md


const frontMatter = {
	sidebar_position: 10
};
const contentTitle = 'Different Notions of Version';

const assets = {

};



const toc = [{
  "value": "Ledger Language Version",
  "id": "ledger-language-version",
  "level": 2
}, {
  "value": "Plutus Core Version",
  "id": "plutus-core-version",
  "level": 2
}, {
  "value": "Builtin Semantics Variant",
  "id": "builtin-semantics-variant",
  "level": 2
}, {
  "value": "Plutus Haskell Package Version",
  "id": "plutus-haskell-package-version",
  "level": 2
}];
function _createMdxContent(props) {
  const _components = {
    a: "a",
    code: "code",
    em: "em",
    h1: "h1",
    h2: "h2",
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
        id: "different-notions-of-version",
        children: "Different Notions of Version"
      })
    }), "\n", (0,jsx_runtime.jsx)(_components.p, {
      children: "There are several different notions of version that Cardano smart contract developers must distinguish."
    }), "\n", (0,jsx_runtime.jsx)(_components.h2, {
      id: "ledger-language-version",
      children: "Ledger Language Version"
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["This is what \"Plutus V1\", \"Plutus V2\", \"Plutus V3\" refer to.\nIt is called \"ledger\" language version because they are ", (0,jsx_runtime.jsx)(_components.em, {
        children: "not"
      }), " really different versions of a language in the sense of programming languages, but different languages from the Cardano ledger's point of view; the ledger handles Plutus V1 vs. V2 vs. V3 differently.\nIn essence, \"Plutus V1\", \"Plutus V2\" and \"Plutus V3\" are tags that the ledger attaches to validators in a transaction."]
    }), "\n", (0,jsx_runtime.jsx)(_components.p, {
      children: "From the ledger's perspective, they are in fact totally different languages:\nthere is no requirement that they be similar or compatible in any way.\nHowever, the \"V1\", \"V2\" and \"V3\" naming scheme is practically useful because in reality they have a lot in common (e.g., the underlying language is Plutus Core and programs are executed by the Plutus Core evaluator, regardless of ledger language version); plus it makes it clear the order that they were introduced and the relationships among them."
    }), "\n", (0,jsx_runtime.jsx)(_components.p, {
      children: "When simply writing a standalone program, say one that takes two integers and returns their sum, or one that implements a Sudoku solver, the notion of ledger language version is completely irrelevant.\nThere is no need (and nowhere) to specify whether you are writing a Plutus V1, or Plutus V2, or Plutus V3 program - again, the concept of ledger language version does not apply to programs themselves.\nYou simply write your code in Plinth, compile it to UPLC, and run it with a UPLC evaluator.\nThis is what we mean by \"they are not really different versions of a language in the sense of programming languages\"."
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["It is only when you write a Plutus ", (0,jsx_runtime.jsx)(_components.em, {
        children: "validator script"
      }), ", put it in a transaction and submit it to the Cardano ledger, that ledger language version becomes relevant. It is relevant in three ways:"]
    }), "\n", (0,jsx_runtime.jsxs)(_components.ul, {
      children: ["\n", (0,jsx_runtime.jsx)(_components.li, {
        children: "Depending on the ledger language version, the ledger will pass different arguments to the validator.\nFor instance, the arguments passed to a Plutus V2 validator include a list of reference inputs of the transaction. This is not passed to a Plutus V1 validator since reference inputs were introduced later than Plutus V1 (specifically, Plutus V1 was introduced in the Alonzo era, while reference inputs were introduced in the Babbage era).\nSimilarly, only Plutus V3 can be used to validate governance actions, since governance actions are introduced in the Conway era and are not part of the pre-Conway era transactions, and thus aren't part of the arguments passed to Plutus V1 or V2 validators."
      }), "\n", (0,jsx_runtime.jsx)(_components.li, {
        children: "At present, a newer ledger language version has access to more builtin functions than an older ledger language version.\nBear in mind that this will change as we plan to make all builtin functions available to all ledger language versions."
      }), "\n", (0,jsx_runtime.jsx)(_components.li, {
        children: "At present, Plutus Core version (explained below) 1.1.0 can only be used with Plutus V3, while Plutus V1 and V2 validators must use Plutus Core 1.0.0.\nThis will also change, as we plan to make all Plutus Core versions compatible with all ledger language versions."
      }), "\n"]
    }), "\n", (0,jsx_runtime.jsx)(_components.p, {
      children: "When do we introduce a new ledger language version?\nA new ledger language version must be introduced when a new ledger era is rolled out, because in a new ledger era, transactions will be different and contain new and/or modified fields, such as governance actions introduced in the Conway era.\nAs a result, new information will need to be passed as arguments to Plutus validators.\nThis necessitates a new ledger language version, because the arguments passed to existing ledger language versions must stay exactly the same, so that existing validators continue to work."
    }), "\n", (0,jsx_runtime.jsx)(_components.p, {
      children: "Previously it was also the case that introducing new builtin functions or new Plutus Core versions necessitate a new ledger language version, but this is no longer the case.\nIntroducing a new ledger language version is very expensive as it must be maintained forever.\nGoing forward we expect the launch of new ledger eras to be the only reason for introducing new ledger language versions."
    }), "\n", (0,jsx_runtime.jsx)(_components.h2, {
      id: "plutus-core-version",
      children: "Plutus Core Version"
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["Plutus Core version is the usual sense of version pertaining to programming languages - in this instance the Plutus Core language.\nSo far there have been two Plutus Core versions: 1.0.0 and 1.1.0.\n1.1.0 adds sums-of-products to the language by introducing two new AST node types: ", (0,jsx_runtime.jsx)(_components.code, {
        children: "Case"
      }), " and ", (0,jsx_runtime.jsx)(_components.code, {
        children: "Constr"
      }), ".\nSee ", (0,jsx_runtime.jsx)(_components.a, {
        href: "https://cips.cardano.org/cip/CIP-0085",
        children: "CIP-85"
      }), " for more details."]
    }), "\n", (0,jsx_runtime.jsx)(_components.p, {
      children: "Note that adding new builtin functions does not require a new Plutus Core version.\nOnce a new builtin function is added, one can simply start using the new builtin function with an existing Plutus Core version."
    }), "\n", (0,jsx_runtime.jsx)(_components.h2, {
      id: "builtin-semantics-variant",
      children: "Builtin Semantics Variant"
    }), "\n", (0,jsx_runtime.jsx)(_components.p, {
      children: "Depending on the protocol version or the ledger language version, or both, we may want to have different behavior of a particular builtin function.\nFor example, we might want to fix a bug but need to retain the old buggy behavior for old evaluations of already-submitted scripts, so we have to have a way of knowing which regime we are in."
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["One example is the builtin function ", (0,jsx_runtime.jsx)(_components.code, {
        children: "consByteString"
      }), ".\nIf the first argument is outside of the range of ", (0,jsx_runtime.jsx)(_components.code, {
        children: "Word8"
      }), ", the original behavior is to wrap it around.\nThe new behavior starting at Plutus V3 is to throw an exception."]
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["When evaluating a standalone program using the ", (0,jsx_runtime.jsx)(_components.code, {
        children: "uplc"
      }), " executable, flag ", (0,jsx_runtime.jsx)(_components.code, {
        children: "-S"
      }), " or ", (0,jsx_runtime.jsx)(_components.code, {
        children: "--builtin-semantics-variant"
      }), " can be used to inform the evaluator which semantics variant to use."]
    }), "\n", (0,jsx_runtime.jsx)(_components.h2, {
      id: "plutus-haskell-package-version",
      children: "Plutus Haskell Package Version"
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["Several Plutus components are regularly released as libraries, such as ", (0,jsx_runtime.jsx)(_components.code, {
        children: "plutus-core"
      }), ", ", (0,jsx_runtime.jsx)(_components.code, {
        children: "plutus-ledger-api"
      }), " and ", (0,jsx_runtime.jsx)(_components.code, {
        children: "plutus-tx-plugin"
      }), ".\nThese packages are published on the ", (0,jsx_runtime.jsx)(_components.a, {
        href: "https://github.com/IntersectMBO/cardano-haskell-packages",
        children: "Cardano Haskell Package repository"
      }), " (CHaP), rather than Hackage, Haskell's default package archive.\nEach release has a version following a standard release versioning scheme, and this is completely orthogonal and irrelevant to all other aforementioned notions of version."]
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