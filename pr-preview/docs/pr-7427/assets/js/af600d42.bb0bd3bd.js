"use strict";
(self["webpackChunkdocusaurus"] = self["webpackChunkdocusaurus"] || []).push([[8306],{

/***/ 4577:
/***/ ((__unused_webpack_module, __webpack_exports__, __webpack_require__) => {

// ESM COMPAT FLAG
__webpack_require__.r(__webpack_exports__);

// EXPORTS
__webpack_require__.d(__webpack_exports__, {
  assets: () => (/* binding */ assets),
  contentTitle: () => (/* binding */ contentTitle),
  "default": () => (/* binding */ MDXContent),
  frontMatter: () => (/* binding */ frontMatter),
  metadata: () => (/* reexport */ site_docs_working_with_scripts_profiling_budget_usage_md_af6_namespaceObject),
  toc: () => (/* binding */ toc)
});

;// ./.docusaurus/docusaurus-plugin-content-docs/default/site-docs-working-with-scripts-profiling-budget-usage-md-af6.json
const site_docs_working_with_scripts_profiling_budget_usage_md_af6_namespaceObject = /*#__PURE__*/JSON.parse('{"id":"working-with-scripts/profiling-budget-usage","title":"Profiling Script Budget Usage","description":"Figuring out why your script takes more CPU or memory units than you expect can be tricky.","source":"@site/docs/working-with-scripts/profiling-budget-usage.md","sourceDirName":"working-with-scripts","slug":"/working-with-scripts/profiling-budget-usage","permalink":"/pr-preview/docs/pr-7427/working-with-scripts/profiling-budget-usage","draft":false,"unlisted":false,"editUrl":"https://github.com/IntersectMBO/plutus/edit/master/doc/docusaurus/docs/working-with-scripts/profiling-budget-usage.md","tags":[],"version":"current","sidebarPosition":30,"frontMatter":{"sidebar_position":30},"sidebar":"tutorialSidebar","previous":{"title":"Other Optimization Techniques","permalink":"/pr-preview/docs/pr-7427/working-with-scripts/other-optimization-techniques"},"next":{"title":"Delve Deeper","permalink":"/pr-preview/docs/pr-7427/category/delve-deeper"}}');
// EXTERNAL MODULE: ./node_modules/react/jsx-runtime.js
var jsx_runtime = __webpack_require__(4848);
// EXTERNAL MODULE: ./node_modules/@mdx-js/react/lib/index.js
var lib = __webpack_require__(8453);
;// ./docs/working-with-scripts/profiling-budget-usage.md


const frontMatter = {
	sidebar_position: 30
};
const contentTitle = 'Profiling Script Budget Usage';

const assets = {

};



const toc = [{
  "value": "Compiling a script for profiling",
  "id": "compiling-a-script-for-profiling",
  "level": 2
}, {
  "value": "Running the script",
  "id": "running-the-script",
  "level": 2
}, {
  "value": "Analyzing the results",
  "id": "analyzing-the-results",
  "level": 2
}];
function _createMdxContent(props) {
  const _components = {
    a: "a",
    blockquote: "blockquote",
    code: "code",
    h1: "h1",
    h2: "h2",
    header: "header",
    p: "p",
    pre: "pre",
    strong: "strong",
    ...(0,lib/* useMDXComponents */.R)(),
    ...props.components
  };
  return (0,jsx_runtime.jsxs)(jsx_runtime.Fragment, {
    children: [(0,jsx_runtime.jsx)(_components.header, {
      children: (0,jsx_runtime.jsx)(_components.h1, {
        id: "profiling-script-budget-usage",
        children: "Profiling Script Budget Usage"
      })
    }), "\n", (0,jsx_runtime.jsx)(_components.p, {
      children: "Figuring out why your script takes more CPU or memory units than you expect can be tricky.\nYou can find out more detail about how these resources are being used in your script by profiling it, and viewing the results in a flamegraph."
    }), "\n", (0,jsx_runtime.jsx)(_components.h2, {
      id: "compiling-a-script-for-profiling",
      children: "Compiling a script for profiling"
    }), "\n", (0,jsx_runtime.jsx)(_components.p, {
      children: "Profiling requires compiling your script differently so that it will emit information that we can use to analyse its performance."
    }), "\n", (0,jsx_runtime.jsxs)(_components.blockquote, {
      children: ["\n", (0,jsx_runtime.jsxs)(_components.p, {
        children: ["📌", " ", (0,jsx_runtime.jsx)(_components.strong, {
          children: "NOTE"
        })]
      }), "\n", (0,jsx_runtime.jsx)(_components.p, {
        children: "As with profiling in other languages, this additional instrumentation can affect how your program is optimized, so its behavior may not be identical to the non-profiled version."
      }), "\n"]
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["To do this, use the ", (0,jsx_runtime.jsx)(_components.code, {
        children: "profile-all"
      }), " and ", (0,jsx_runtime.jsx)(_components.code, {
        children: "conservative-optimisation"
      }), " plugin flags:"]
    }), "\n", (0,jsx_runtime.jsx)(_components.pre, {
      children: (0,jsx_runtime.jsx)(_components.code, {
        className: "language-haskell",
        children: "{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:profile-all #-}\n{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:conservative-optimisation #-}\n"
      })
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["This instructs the plugin to insert profiling instrumentation for all functions.\nIn the future there may be the option to profile a more targeted set of functions.\nThe ", (0,jsx_runtime.jsx)(_components.code, {
        children: "conservative-optimisation"
      }), " flag makes sure that any inserted profiling instrumentation code would not be optimized away during PlutusTx compilation."]
    }), "\n", (0,jsx_runtime.jsx)(_components.h2, {
      id: "running-the-script",
      children: "Running the script"
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["You can run a script using the ", (0,jsx_runtime.jsx)(_components.code, {
        children: "uplc"
      }), " executable, which can be downloaded from each ", (0,jsx_runtime.jsx)(_components.a, {
        href: "https://github.com/IntersectMBO/plutus/releases",
        children: "Plutus release"
      }), ".\nIf no pre-built executable is available for your architecture, you can build it from source using ", (0,jsx_runtime.jsx)(_components.code, {
        children: "cabal build uplc"
      }), "."]
    }), "\n", (0,jsx_runtime.jsx)(_components.p, {
      children: "Keep in mind that the budget is consumed as the script runs, so you need both the script and all its arguments, and create a fully applied script by applying the script to all arguments."
    }), "\n", (0,jsx_runtime.jsx)(_components.p, {
      children: "Given a script and its arguments, a fully applied script can be obtained via"
    }), "\n", (0,jsx_runtime.jsx)(_components.pre, {
      children: (0,jsx_runtime.jsx)(_components.code, {
        className: "language-bash",
        children: "uplc apply script arg1 arg2 ... argn\n"
      })
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["Once you have the fully applied script, you can evaluate it using the ", (0,jsx_runtime.jsx)(_components.code, {
        children: "uplc"
      }), " executable, with a command like the one below:"]
    }), "\n", (0,jsx_runtime.jsx)(_components.pre, {
      children: (0,jsx_runtime.jsx)(_components.code, {
        className: "language-bash",
        children: "uplc evaluate -i fully-applied-script.flat --if flat --trace-mode LogsWithBudgets -o logs\n"
      })
    }), "\n", (0,jsx_runtime.jsx)(_components.p, {
      children: "This runs the script using the trace mode that emits budget information, and puts the resulting logs in a file.\nThis will be a CSV file with three columns: a message indicating which function we are entering or exiting; the cumulative CPU used at that time; and the cumulative memory used at that time."
    }), "\n", (0,jsx_runtime.jsx)(_components.h2, {
      id: "analyzing-the-results",
      children: "Analyzing the results"
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["We can then convert the logs into a flamegraph using the standard ", (0,jsx_runtime.jsx)(_components.code, {
        children: "flamegraph.pl"
      }), " tool.\nThe ", (0,jsx_runtime.jsx)(_components.code, {
        children: "traceToStacks"
      }), " executable turns the logs into a format that ", (0,jsx_runtime.jsx)(_components.code, {
        children: "flamegraph.pl"
      }), " understands"]
    }), "\n", (0,jsx_runtime.jsx)(_components.pre, {
      children: (0,jsx_runtime.jsx)(_components.code, {
        className: "language-bash",
        children: "cat logs | traceToStacks | flamegraph.pl > cpu.svg\ncat logs | traceToStacks --column 2 | flamegraph.pl > mem.svg\n"
      })
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["Since ", (0,jsx_runtime.jsx)(_components.code, {
        children: "flamegraph.pl"
      }), " can only handle one metric at a time, ", (0,jsx_runtime.jsx)(_components.code, {
        children: "traceToStacks"
      }), " has a ", (0,jsx_runtime.jsx)(_components.code, {
        children: "--column"
      }), " argument to select the other column if you want to get a memory flamegraph."]
    }), "\n", (0,jsx_runtime.jsx)(_components.p, {
      children: "You can then view the resulting SVGs in a viewer of your choice, such as a web browser."
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["Alternatively, there are other, more powerful, tools that understand the format produced by ", (0,jsx_runtime.jsx)(_components.code, {
        children: "traceToStacks"
      }), ", such as ", (0,jsx_runtime.jsx)(_components.a, {
        href: "https://www.speedscope.app/",
        children: "speedscope"
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