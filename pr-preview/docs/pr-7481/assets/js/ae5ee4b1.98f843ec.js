"use strict";
(self["webpackChunkdocusaurus"] = self["webpackChunkdocusaurus"] || []).push([[7019],{

/***/ 1519:
/***/ ((__unused_webpack_module, __webpack_exports__, __webpack_require__) => {

// ESM COMPAT FLAG
__webpack_require__.r(__webpack_exports__);

// EXPORTS
__webpack_require__.d(__webpack_exports__, {
  assets: () => (/* binding */ assets),
  contentTitle: () => (/* binding */ contentTitle),
  "default": () => (/* binding */ MDXContent),
  frontMatter: () => (/* binding */ frontMatter),
  metadata: () => (/* reexport */ site_docs_using_plinth_compiling_plinth_md_ae5_namespaceObject),
  toc: () => (/* binding */ toc)
});

;// ./.docusaurus/docusaurus-plugin-content-docs/default/site-docs-using-plinth-compiling-plinth-md-ae5.json
const site_docs_using_plinth_compiling_plinth_md_ae5_namespaceObject = /*#__PURE__*/JSON.parse('{"id":"using-plinth/compiling-plinth","title":"Compiling Plinth","description":"The Plinth compiler is a GHC plugin, provided by the plutus-tx-plugin package.","source":"@site/docs/using-plinth/compiling-plinth.md","sourceDirName":"using-plinth","slug":"/using-plinth/compiling-plinth","permalink":"/pr-preview/docs/pr-7481/using-plinth/compiling-plinth","draft":false,"unlisted":false,"editUrl":"https://github.com/IntersectMBO/plutus/edit/master/doc/docusaurus/docs/using-plinth/compiling-plinth.md","tags":[],"version":"current","sidebarPosition":10,"frontMatter":{"sidebar_position":10},"sidebar":"tutorialSidebar","previous":{"title":"Environment Setup","permalink":"/pr-preview/docs/pr-7481/using-plinth/environment-setup"},"next":{"title":"Lifting Values into CompiledCode","permalink":"/pr-preview/docs/pr-7481/using-plinth/lifting"}}');
// EXTERNAL MODULE: ./node_modules/react/jsx-runtime.js
var jsx_runtime = __webpack_require__(4848);
// EXTERNAL MODULE: ./node_modules/@mdx-js/react/lib/index.js
var lib = __webpack_require__(8453);
;// ./docs/using-plinth/compiling-plinth.md


const frontMatter = {
	sidebar_position: 10
};
const contentTitle = 'Compiling Plinth';

const assets = {

};



const toc = [{
  "value": "Compiling Using Template Haskell (Preferred)",
  "id": "compiling-using-template-haskell-preferred",
  "level": 2
}, {
  "value": "Compiling Using GHC Flag",
  "id": "compiling-using-ghc-flag",
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
        id: "compiling-plinth",
        children: "Compiling Plinth"
      })
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["The Plinth compiler is a GHC plugin, provided by the ", (0,jsx_runtime.jsx)(_components.code, {
        children: "plutus-tx-plugin"
      }), " package.\nThere are two ways to invoke the plugin: via Template Haskell (preferred) or using a GHC flag."]
    }), "\n", (0,jsx_runtime.jsx)(_components.p, {
      children: "Let’s assume we want to compile the following code:"
    }), "\n", (0,jsx_runtime.jsx)(_components.pre, {
      children: (0,jsx_runtime.jsx)(_components.code, {
        className: "language-haskell",
        children: "module A where\n\nimport qualified PlutusTx.Prelude as PlutusTx\n\nmyPlutusTxCode :: Integer -> Integer\nmyPlutusTxCode x = x PlutusTx.+ 1\n"
      })
    }), "\n", (0,jsx_runtime.jsxs)(_components.blockquote, {
      children: ["\n", (0,jsx_runtime.jsxs)(_components.p, {
        children: ["📌", " ", (0,jsx_runtime.jsx)(_components.strong, {
          children: "NOTE"
        })]
      }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
        children: ["There are some GHC extensions, flags and pragmas recommended for modules containing Plinth code, but these are omitted here.\nYou can find more information in ", (0,jsx_runtime.jsx)(_components.a, {
          href: "/pr-preview/docs/pr-7481/using-plinth/extensions-flags-pragmas",
          children: "GHC Extensions, Flags and Pragmas"
        }), "."]
      }), "\n"]
    }), "\n", (0,jsx_runtime.jsx)(_components.h2, {
      id: "compiling-using-template-haskell-preferred",
      children: "Compiling Using Template Haskell (Preferred)"
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["Here's how to compile ", (0,jsx_runtime.jsx)(_components.code, {
        children: "myPlutusTxCode"
      }), " using Template Haskell:"]
    }), "\n", (0,jsx_runtime.jsx)(_components.pre, {
      children: (0,jsx_runtime.jsx)(_components.code, {
        className: "language-haskell",
        children: "{-# LANGUAGE TemplateHaskell #-}\nmodule B where\n\nimport PlutusTx.Code (CompiledCode)\nimport PlutusTx.TH (compile)\n\nmyPlutusTxCodeCompiled :: CompiledCode (Integer -> Integer)\nmyPlutusTxCodeCompiled = $$(compile [|| myPlutusTxCode ||])\n"
      })
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["Under the hood, it uses ", (0,jsx_runtime.jsx)(_components.a, {
        href: "https://hackage.haskell.org/package/template-haskell/docs/Language-Haskell-TH-Syntax.html#v:addCorePlugin",
        children: (0,jsx_runtime.jsx)(_components.code, {
          children: "addCorePlugin"
        })
      }), " from the ", (0,jsx_runtime.jsx)(_components.code, {
        children: "template-haskell"
      }), " package to install the plugin into the compilation pipeline."]
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["You can then compile module ", (0,jsx_runtime.jsx)(_components.code, {
        children: "B"
      }), " as you would any regular Haskell module.\nThe resulting ", (0,jsx_runtime.jsx)(_components.code, {
        children: "CompiledCode"
      }), " contains the UPLC code, and also includes PIR for debugging."]
    }), "\n", (0,jsx_runtime.jsx)(_components.p, {
      children: "Template Haskell is a complicated piece of machinery, but as you can see, you need to understand almost none of it for the purpose of compiling Plinth."
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["This method is preferred since it can leverage Template Haskell's ", (0,jsx_runtime.jsx)(_components.a, {
        href: "https://hackage.haskell.org/package/template-haskell/docs/Language-Haskell-TH.html#v:location",
        children: (0,jsx_runtime.jsx)(_components.code, {
          children: "location"
        })
      }), " function to pass the location of ", (0,jsx_runtime.jsx)(_components.code, {
        children: "$$(compile [|| ... ||])"
      }), " to the plugin, which is used in error messages."]
    }), "\n", (0,jsx_runtime.jsx)(_components.h2, {
      id: "compiling-using-ghc-flag",
      children: "Compiling Using GHC Flag"
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["An alternative way to compile ", (0,jsx_runtime.jsx)(_components.code, {
        children: "myPlutusTxCode"
      }), " is by using the ", (0,jsx_runtime.jsx)(_components.code, {
        children: "-fplugin"
      }), " GHC flag, which installs a plugin into the pipeline.\nUse this flag with the ", (0,jsx_runtime.jsx)(_components.code, {
        children: "plc"
      }), " function:"]
    }), "\n", (0,jsx_runtime.jsx)(_components.pre, {
      children: (0,jsx_runtime.jsx)(_components.code, {
        className: "language-haskell",
        children: "{-# OPTIONS_GHC -fplugin PlutusTx.Plugin #-}\nmodule B where\n\nimport Data.Proxy\nimport PlutusTx.Code (CompiledCode)\nimport PlutusTx.Plugin (plc)\n\nmyPlutusTxCodeCompiled :: CompiledCode (Integer -> Integer)\nmyPlutusTxCodeCompiled = plc (Proxy @\"location info\") myPlutusTxCode\n"
      })
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["Here you can manually provide the location info to be included in error messages, but it's not essential, especially if ", (0,jsx_runtime.jsx)(_components.code, {
        children: "plc"
      }), " is only called once in the module, since there won't be any confusion about which ", (0,jsx_runtime.jsx)(_components.code, {
        children: "plc"
      }), " is causing the issue if the module fails to compile."]
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["The ", (0,jsx_runtime.jsx)(_components.code, {
        children: "-fplugin"
      }), " flag must be used on every module that invokes ", (0,jsx_runtime.jsx)(_components.code, {
        children: "plc"
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