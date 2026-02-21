"use strict";
(self["webpackChunkdocusaurus"] = self["webpackChunkdocusaurus"] || []).push([[9629],{

/***/ 3818:
/***/ ((__unused_webpack_module, __webpack_exports__, __webpack_require__) => {

// ESM COMPAT FLAG
__webpack_require__.r(__webpack_exports__);

// EXPORTS
__webpack_require__.d(__webpack_exports__, {
  assets: () => (/* binding */ assets),
  contentTitle: () => (/* binding */ contentTitle),
  "default": () => (/* binding */ MDXContent),
  frontMatter: () => (/* binding */ frontMatter),
  metadata: () => (/* reexport */ site_docs_using_plinth_inspecting_md_4e6_namespaceObject),
  toc: () => (/* binding */ toc)
});

;// ./.docusaurus/docusaurus-plugin-content-docs/default/site-docs-using-plinth-inspecting-md-4e6.json
const site_docs_using_plinth_inspecting_md_4e6_namespaceObject = /*#__PURE__*/JSON.parse('{"id":"using-plinth/inspecting","title":"Inspecting Compilation and Compiled Code","description":"On this page, you’ll learn how to look into the compilation of Plinth and the resulting compiled code, which you might want to do for reasons such as debugging and tuning.","source":"@site/docs/using-plinth/inspecting.md","sourceDirName":"using-plinth","slug":"/using-plinth/inspecting","permalink":"/pr-preview/docs/pr-7547/using-plinth/inspecting","draft":false,"unlisted":false,"editUrl":"https://github.com/IntersectMBO/plutus/edit/master/doc/docusaurus/docs/using-plinth/inspecting.md","tags":[],"version":"current","sidebarPosition":30,"frontMatter":{"sidebar_position":30},"sidebar":"tutorialSidebar","previous":{"title":"Special Functions and Types","permalink":"/pr-preview/docs/pr-7547/using-plinth/special-functions-and-types"},"next":{"title":"CLI tool for Plutus","permalink":"/pr-preview/docs/pr-7547/using-plinth/cli-plutus"}}');
// EXTERNAL MODULE: ./node_modules/react/jsx-runtime.js
var jsx_runtime = __webpack_require__(4848);
// EXTERNAL MODULE: ./node_modules/@mdx-js/react/lib/index.js
var lib = __webpack_require__(8453);
;// ./docs/using-plinth/inspecting.md


const frontMatter = {
	sidebar_position: 30
};
const contentTitle = 'Inspecting Compilation and Compiled Code';

const assets = {

};



const toc = [{
  "value": "Inspecting the Compilation",
  "id": "inspecting-the-compilation",
  "level": 2
}, {
  "value": "Inspecting the Compiled Code",
  "id": "inspecting-the-compiled-code",
  "level": 2
}];
function _createMdxContent(props) {
  const _components = {
    a: "a",
    code: "code",
    h1: "h1",
    h2: "h2",
    header: "header",
    li: "li",
    p: "p",
    pre: "pre",
    table: "table",
    tbody: "tbody",
    td: "td",
    th: "th",
    thead: "thead",
    tr: "tr",
    ul: "ul",
    ...(0,lib/* useMDXComponents */.R)(),
    ...props.components
  };
  return (0,jsx_runtime.jsxs)(jsx_runtime.Fragment, {
    children: [(0,jsx_runtime.jsx)(_components.header, {
      children: (0,jsx_runtime.jsx)(_components.h1, {
        id: "inspecting-compilation-and-compiled-code",
        children: "Inspecting Compilation and Compiled Code"
      })
    }), "\n", (0,jsx_runtime.jsx)(_components.p, {
      children: "On this page, you’ll learn how to look into the compilation of Plinth and the resulting compiled code, which you might want to do for reasons such as debugging and tuning."
    }), "\n", (0,jsx_runtime.jsx)(_components.h2, {
      id: "inspecting-the-compilation",
      children: "Inspecting the Compilation"
    }), "\n", (0,jsx_runtime.jsx)(_components.p, {
      children: "In the event of a compilation failure, a trace of compilation steps leading to the problematic GHC Core expression is printed.\nThis is comparable to the stack trace from a program encountering an uncaught exception.\nFor example, if you use an unsupported Haskell feature, causing the compilation to fail, this trace can often help you identify where it appears in the source code."
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["Another way of inspecting the compilation is by using the ", (0,jsx_runtime.jsx)(_components.code, {
        children: "dump-compilation-trace"
      }), " plugin flag:"]
    }), "\n", (0,jsx_runtime.jsx)(_components.pre, {
      children: (0,jsx_runtime.jsx)(_components.code, {
        className: "language-haskell",
        children: "{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:dump-compilation-trace #-}\n"
      })
    }), "\n", (0,jsx_runtime.jsx)(_components.p, {
      children: "This compilation trace has two main differences from the previously mentioned trace:"
    }), "\n", (0,jsx_runtime.jsxs)(_components.ul, {
      children: ["\n", (0,jsx_runtime.jsx)(_components.li, {
        children: "It prints every single step taken by the compiler, as the compilation proceeds, rather than just the trace leading to the failure."
      }), "\n", (0,jsx_runtime.jsx)(_components.li, {
        children: "It can be used to show the trace whether the compilation succeeded or failed.\nThis is convenient because sometimes you might want to compare the trace of a failed compilation against the trace of a succeeded compilation to figure out where it went wrong."
      }), "\n"]
    }), "\n", (0,jsx_runtime.jsx)(_components.p, {
      children: "In the compilation trace, to make it easier to figure out how the compilation got to a certain point, every step is annotated with an ID along with the ID of the parent step."
    }), "\n", (0,jsx_runtime.jsx)(_components.h2, {
      id: "inspecting-the-compiled-code",
      children: "Inspecting the Compiled Code"
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["A ", (0,jsx_runtime.jsx)(_components.code, {
        children: "CompiledCode"
      }), " obtained through normal compilation includes a UPLC program along with the corresponding PIR program.\nPIR is an intermediate representation used by the Plinth compiler.\nIt is much more readable than UPLC, so for tasks such as debugging and performance tuning, it is usually more helpful to inspect PIR, but there are also instances where looking into UPLC directly is necessary."]
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["The PIR and UPLC programs can be retrieved from the ", (0,jsx_runtime.jsx)(_components.code, {
        children: "CompiledCode"
      }), " via ", (0,jsx_runtime.jsx)(_components.code, {
        children: "getPirNoAnn"
      }), " and ", (0,jsx_runtime.jsx)(_components.code, {
        children: "getPlcNoAnn"
      }), " from ", (0,jsx_runtime.jsx)(_components.a, {
        href: "https://plutus.cardano.intersectmbo.org/haddock/latest/plutus-tx/PlutusTx-Code.html",
        children: (0,jsx_runtime.jsx)(_components.code, {
          children: "PlutusTx.Code"
        })
      }), ".\nThe annotations are usually not needed, but if you do need them, use ", (0,jsx_runtime.jsx)(_components.code, {
        children: "getPir"
      }), " and ", (0,jsx_runtime.jsx)(_components.code, {
        children: "getPlc"
      }), " instead."]
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["The ", (0,jsx_runtime.jsx)(_components.code, {
        children: "plutus-core"
      }), " library provides several ways for pretty-printing PIR and UPLC programs.\nThere are two main configuration options for pretty-printing:"]
    }), "\n", (0,jsx_runtime.jsxs)(_components.ul, {
      children: ["\n", (0,jsx_runtime.jsx)(_components.li, {
        children: "Choosing between the classic syntax or a more readable syntax."
      }), "\n", (0,jsx_runtime.jsx)(_components.li, {
        children: "Choosing whether to show uniques.\nUniques are numerical identifiers assigned to variable names; while they ensure unambiguity, they can introduce clutter."
      }), "\n"]
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["The following table shows the functions for pretty-printing PIR and UPLC programs.\nAll these are from the ", (0,jsx_runtime.jsx)(_components.a, {
        href: "https://plutus.cardano.intersectmbo.org/haddock/latest/plutus-core/PlutusCore-Pretty.html",
        children: (0,jsx_runtime.jsx)(_components.code, {
          children: "PlutusCore.Pretty"
        })
      }), " module."]
    }), "\n", (0,jsx_runtime.jsxs)(_components.table, {
      children: [(0,jsx_runtime.jsx)(_components.thead, {
        children: (0,jsx_runtime.jsxs)(_components.tr, {
          children: [(0,jsx_runtime.jsx)(_components.th, {}), (0,jsx_runtime.jsx)(_components.th, {
            children: "Classic Syntax"
          }), (0,jsx_runtime.jsx)(_components.th, {
            children: "Readable Syntax"
          })]
        })
      }), (0,jsx_runtime.jsxs)(_components.tbody, {
        children: [(0,jsx_runtime.jsxs)(_components.tr, {
          children: [(0,jsx_runtime.jsx)(_components.td, {
            children: "No Uniques"
          }), (0,jsx_runtime.jsx)(_components.td, {
            children: (0,jsx_runtime.jsx)(_components.code, {
              children: "prettyClassicSimple"
            })
          }), (0,jsx_runtime.jsx)(_components.td, {
            children: (0,jsx_runtime.jsx)(_components.code, {
              children: "prettyReadableSimple"
            })
          })]
        }), (0,jsx_runtime.jsxs)(_components.tr, {
          children: [(0,jsx_runtime.jsx)(_components.td, {
            children: "With Uniques"
          }), (0,jsx_runtime.jsx)(_components.td, {
            children: (0,jsx_runtime.jsx)(_components.code, {
              children: "prettyClassic"
            })
          }), (0,jsx_runtime.jsx)(_components.td, {
            children: (0,jsx_runtime.jsx)(_components.code, {
              children: "prettyReadable"
            })
          })]
        })]
      })]
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