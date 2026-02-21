"use strict";
(self["webpackChunkdocusaurus"] = self["webpackChunkdocusaurus"] || []).push([[4795],{

/***/ 518:
/***/ ((__unused_webpack_module, __webpack_exports__, __webpack_require__) => {

// ESM COMPAT FLAG
__webpack_require__.r(__webpack_exports__);

// EXPORTS
__webpack_require__.d(__webpack_exports__, {
  assets: () => (/* binding */ assets),
  contentTitle: () => (/* binding */ contentTitle),
  "default": () => (/* binding */ MDXContent),
  frontMatter: () => (/* binding */ frontMatter),
  metadata: () => (/* reexport */ site_docs_working_with_scripts_simplifying_before_compilation_md_90e_namespaceObject),
  toc: () => (/* binding */ toc)
});

;// ./.docusaurus/docusaurus-plugin-content-docs/default/site-docs-working-with-scripts-simplifying-before-compilation-md-90e.json
const site_docs_working_with_scripts_simplifying_before_compilation_md_90e_namespaceObject = /*#__PURE__*/JSON.parse('{"id":"working-with-scripts/simplifying-before-compilation","title":"Simplifying Code Before Compilation","description":"Much like in regular Haskell, simplifying or expanding certain Plinth code before compilation can make it more efficient.","source":"@site/docs/working-with-scripts/simplifying-before-compilation.md","sourceDirName":"working-with-scripts","slug":"/working-with-scripts/simplifying-before-compilation","permalink":"/pr-preview/docs/pr-7463/working-with-scripts/simplifying-before-compilation","draft":false,"unlisted":false,"editUrl":"https://github.com/IntersectMBO/plutus/edit/master/doc/docusaurus/docs/working-with-scripts/simplifying-before-compilation.md","tags":[],"version":"current","sidebarPosition":22,"frontMatter":{"sidebar_position":22},"sidebar":"tutorialSidebar","previous":{"title":"Optimizing Scripts with asData","permalink":"/pr-preview/docs/pr-7463/working-with-scripts/optimizing-scripts-with-asData"},"next":{"title":"Compile Time Evaluation","permalink":"/pr-preview/docs/pr-7463/working-with-scripts/compile-time-evaluation"}}');
// EXTERNAL MODULE: ./node_modules/react/jsx-runtime.js
var jsx_runtime = __webpack_require__(4848);
// EXTERNAL MODULE: ./node_modules/@mdx-js/react/lib/index.js
var lib = __webpack_require__(8453);
;// ./docs/working-with-scripts/simplifying-before-compilation.md


const frontMatter = {
	sidebar_position: 22
};
const contentTitle = 'Simplifying Code Before Compilation';

const assets = {

};



const toc = [{
  "value": "Template Haskell",
  "id": "template-haskell",
  "level": 2
}, {
  "value": "GHC Plugins",
  "id": "ghc-plugins",
  "level": 2
}];
function _createMdxContent(props) {
  const _components = {
    a: "a",
    code: "code",
    h1: "h1",
    h2: "h2",
    header: "header",
    p: "p",
    pre: "pre",
    ...(0,lib/* useMDXComponents */.R)(),
    ...props.components
  };
  return (0,jsx_runtime.jsxs)(jsx_runtime.Fragment, {
    children: [(0,jsx_runtime.jsx)(_components.header, {
      children: (0,jsx_runtime.jsx)(_components.h1, {
        id: "simplifying-code-before-compilation",
        children: "Simplifying Code Before Compilation"
      })
    }), "\n", (0,jsx_runtime.jsx)(_components.p, {
      children: "Much like in regular Haskell, simplifying or expanding certain Plinth code before compilation can make it more efficient."
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["As an example, suppose you want to call ", (0,jsx_runtime.jsx)(_components.code, {
        children: "PlutusTx.List.tail"
      }), " on a list ", (0,jsx_runtime.jsx)(_components.code, {
        children: "n"
      }), " times in Plinth.\nYou can implement it using a fold:"]
    }), "\n", (0,jsx_runtime.jsx)(_components.pre, {
      children: (0,jsx_runtime.jsx)(_components.code, {
        className: "language-haskell",
        children: "ntails :: Integer -> [a] -> [a]\nntails =\n  PlutusTx.List.foldl\n    (\\acc _ -> PlutusTx.List.tail . acc)\n    id\n    (PlutusTx.replicate n ())\n"
      })
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["This works, but if the value of ", (0,jsx_runtime.jsx)(_components.code, {
        children: "n"
      }), " is known statically, say ", (0,jsx_runtime.jsx)(_components.code, {
        children: "n = 5"
      }), ", it may be better to use the following direct implementation:"]
    }), "\n", (0,jsx_runtime.jsx)(_components.pre, {
      children: (0,jsx_runtime.jsx)(_components.code, {
        className: "language-haskell",
        children: "tails5 :: [a] -> [a]\ntails5 =\n  PlutusTx.List.tail\n    . PlutusTx.List.tail\n    . PlutusTx.List.tail\n    . PlutusTx.List.tail\n    . PlutusTx.List.tail\n"
      })
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["It may cause the script to increase in size if ", (0,jsx_runtime.jsx)(_components.code, {
        children: "n"
      }), " is large, but this has less execution overhead, so the script will be cheaper to execute."]
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["Even if ", (0,jsx_runtime.jsx)(_components.code, {
        children: "n"
      }), " is not known statically, you can still take advantage of ", (0,jsx_runtime.jsx)(_components.code, {
        children: "tails5"
      }), ", and perform ", (0,jsx_runtime.jsx)(_components.code, {
        children: "ntails"
      }), " 5 elements at a time, much like ", (0,jsx_runtime.jsx)(_components.a, {
        href: "https://en.wikipedia.org/wiki/Loop_unrolling",
        children: "loop unrolling"
      }), ":"]
    }), "\n", (0,jsx_runtime.jsx)(_components.pre, {
      children: (0,jsx_runtime.jsx)(_components.code, {
        className: "language-haskell",
        children: "ntails :: Integer -> [a] -> [a]\nntails n\n  | n >= 5 = nTails (n - 5) . tails5\n  | otherwise =\n      PlutusTx.List.foldl\n        (\\acc _ -> PlutusTx.List.tail . acc)\n        id\n        (PlutusTx.replicate n ())\n"
      })
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["You can write code like ", (0,jsx_runtime.jsx)(_components.code, {
        children: "tails5"
      }), " by hand, but in more complex cases, you can instead use standard Haskell techniques for generating and manipulating source code, such as Template Haskell and GHC plugins.\nAfter all, Plinth is a subset of Haskell."]
    }), "\n", (0,jsx_runtime.jsx)(_components.h2, {
      id: "template-haskell",
      children: "Template Haskell"
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["The most common method to programmatically generate code like ", (0,jsx_runtime.jsx)(_components.code, {
        children: "tails5"
      }), " is through Template Haskell.\nThe following ", (0,jsx_runtime.jsx)(_components.code, {
        children: "ntailsTH"
      }), " function generates a Template Haskell expression for applying ", (0,jsx_runtime.jsx)(_components.code, {
        children: "tail"
      }), " ", (0,jsx_runtime.jsx)(_components.code, {
        children: "n"
      }), " times, for any ", (0,jsx_runtime.jsx)(_components.code, {
        children: "n"
      }), " that is statically known:"]
    }), "\n", (0,jsx_runtime.jsx)(_components.pre, {
      children: (0,jsx_runtime.jsx)(_components.code, {
        className: "language-haskell",
        children: "import qualified Language.Haskell.TH as TH\n\nntailsTH :: forall a. Int -> TH.Code TH.Q ([a] -> [a])\nntailsTH n =\n  Data.List.foldl'\n    (\\acc _ -> [|| PlutusTx.tail . $$acc ||])\n    [|| id ||]\n    (Data.List.replicate n ())\n"
      })
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["It's worth noting that ", (0,jsx_runtime.jsx)(_components.code, {
        children: "foldl'"
      }), " and ", (0,jsx_runtime.jsx)(_components.code, {
        children: "replicate"
      }), " are executed in Haskell for constructing the expression (rather than being compiled to UPLC), so we can use the ones in ", (0,jsx_runtime.jsx)(_components.code, {
        children: "Data.List"
      }), " rather than ", (0,jsx_runtime.jsx)(_components.code, {
        children: "PlutusTx.List"
      }), " (though the latter also works)."]
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["Then we can write ", (0,jsx_runtime.jsx)(_components.code, {
        children: "tails5"
      }), " as"]
    }), "\n", (0,jsx_runtime.jsx)(_components.pre, {
      children: (0,jsx_runtime.jsx)(_components.code, {
        className: "language-haskell",
        children: "tails5 :: [a] -> [a]\ntails5 = $$(ntailsTH 5)\n"
      })
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["Since this is nothing but standard Template Haskell usage, we'll keep it concise here.\nSome good resources to learn more about Template Haskell include the ", (0,jsx_runtime.jsx)(_components.a, {
        href: "https://wiki.haskell.org/Template_Haskell",
        children: "Template Haskell page on HaskellWiki"
      }), " (which has links to further resources), ", (0,jsx_runtime.jsx)(_components.a, {
        href: "https://markkarpov.com/tutorial/th",
        children: "Template Haskell tutorial"
      }), " by Mark Karpov, and ", (0,jsx_runtime.jsx)(_components.a, {
        href: "https://serokell.io/blog/introduction-to-template-haskell",
        children: "Introduction to Template Haskell"
      }), " by Heitor Toledo Lassarote de Paula."]
    }), "\n", (0,jsx_runtime.jsx)(_components.h2, {
      id: "ghc-plugins",
      children: "GHC Plugins"
    }), "\n", (0,jsx_runtime.jsx)(_components.p, {
      children: "If you need something even more powerful and flexible than Template Haskell, you can write your own GHC plugin to customize the transformation and compilation of certain parts of your code.\nHowever, this is a more advanced tool with greater complexity, which is further compounded by GHC's unstable API, making it difficult to support multiple major GHC versions.\nYou should rarely need to do this, as Template Haskell should meet most requirements."
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["If you do decide to write your own GHC plugin, keep in mind that the Plinth compiler is also a GHC plugin, so be careful of the orders in which the two plugins are invoked, especially since ", (0,jsx_runtime.jsx)(_components.a, {
        href: "https://gitlab.haskell.org/ghc/ghc/-/issues/17884",
        children: "the order has changed since GHC 9.4"
      }), "."]
    }), "\n", (0,jsx_runtime.jsx)(_components.p, {
      children: "Finally, keep in mind that doing what's described in this page is not always desirable, since although it reduces script execution costs, it often increases script sizes.\nFor Plutus scripts, size is a much more valuable resource than for general-purpose programs, since Cardano has strict script size and transaction size limits."
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