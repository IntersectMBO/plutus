"use strict";
(self["webpackChunkdocusaurus"] = self["webpackChunkdocusaurus"] || []).push([[1836],{

/***/ 7325:
/***/ ((__unused_webpack_module, __webpack_exports__, __webpack_require__) => {

// ESM COMPAT FLAG
__webpack_require__.r(__webpack_exports__);

// EXPORTS
__webpack_require__.d(__webpack_exports__, {
  assets: () => (/* binding */ assets),
  contentTitle: () => (/* binding */ contentTitle),
  "default": () => (/* binding */ MDXContent),
  frontMatter: () => (/* binding */ frontMatter),
  metadata: () => (/* reexport */ site_docs_using_plinth_special_functions_and_types_md_394_namespaceObject),
  toc: () => (/* binding */ toc)
});

;// ./.docusaurus/docusaurus-plugin-content-docs/default/site-docs-using-plinth-special-functions-and-types-md-394.json
const site_docs_using_plinth_special_functions_and_types_md_394_namespaceObject = /*#__PURE__*/JSON.parse('{"id":"using-plinth/special-functions-and-types","title":"Special Functions and Types","description":"Normally, the Plinth compiler compiles a Haskell identifier by obtaining and compiling its definition (also known as unfolding), and creating a term binding in PIR, an intermediate representation used by the Plinth compiler.","source":"@site/docs/using-plinth/special-functions-and-types.md","sourceDirName":"using-plinth","slug":"/using-plinth/special-functions-and-types","permalink":"/pr-preview/docs/pr-7473/using-plinth/special-functions-and-types","draft":false,"unlisted":false,"editUrl":"https://github.com/IntersectMBO/plutus/edit/master/doc/docusaurus/docs/using-plinth/special-functions-and-types.md","tags":[],"version":"current","sidebarPosition":25,"frontMatter":{"sidebar_position":25},"sidebar":"tutorialSidebar","previous":{"title":"GHC Extensions, Flags and Pragmas","permalink":"/pr-preview/docs/pr-7473/using-plinth/extensions-flags-pragmas"},"next":{"title":"Inspecting Compilation and Compiled Code","permalink":"/pr-preview/docs/pr-7473/using-plinth/inspecting"}}');
// EXTERNAL MODULE: ./node_modules/react/jsx-runtime.js
var jsx_runtime = __webpack_require__(4848);
// EXTERNAL MODULE: ./node_modules/@mdx-js/react/lib/index.js
var lib = __webpack_require__(8453);
;// ./docs/using-plinth/special-functions-and-types.md


const frontMatter = {
	sidebar_position: 25
};
const contentTitle = 'Special Functions and Types';

const assets = {

};



const toc = [{
  "value": "Builtin Functions and Types",
  "id": "builtin-functions-and-types",
  "level": 2
}, {
  "value": "<code>PlutusTx.Bool.&amp;&amp;</code> and <code>PlutusTx.Bool.||</code>",
  "id": "plutustxbool-and-plutustxbool",
  "level": 2
}, {
  "value": "<code>IsString</code> Instances",
  "id": "isstring-instances",
  "level": 2
}, {
  "value": "Builtin ByteString literals",
  "id": "builtin-bytestring-literals",
  "level": 3
}];
function _createMdxContent(props) {
  const _components = {
    a: "a",
    admonition: "admonition",
    blockquote: "blockquote",
    code: "code",
    em: "em",
    h1: "h1",
    h2: "h2",
    h3: "h3",
    header: "header",
    li: "li",
    p: "p",
    pre: "pre",
    strong: "strong",
    ul: "ul",
    ...(0,lib/* useMDXComponents */.R)(),
    ...props.components
  }, {Details} = _components;
  if (!Details) _missingMdxReference("Details", true);
  return (0,jsx_runtime.jsxs)(jsx_runtime.Fragment, {
    children: [(0,jsx_runtime.jsx)(_components.header, {
      children: (0,jsx_runtime.jsx)(_components.h1, {
        id: "special-functions-and-types",
        children: "Special Functions and Types"
      })
    }), "\n", (0,jsx_runtime.jsx)(_components.p, {
      children: "Normally, the Plinth compiler compiles a Haskell identifier by obtaining and compiling its definition (also known as unfolding), and creating a term binding in PIR, an intermediate representation used by the Plinth compiler.\nTypes are compiled in a similar manner, by compiling the type's definition and generating a type or datatype binding in PIR."
    }), "\n", (0,jsx_runtime.jsx)(_components.p, {
      children: "However, there are certain special functions and types that aren't compiled this way.\nRather, they are handled specially and directly converted to terms or types in PIR.\nIt is useful to be aware of these, as these functions and types work differently than regular user-defined functions and types, and cannot be defined in user space."
    }), "\n", (0,jsx_runtime.jsx)(_components.h2, {
      id: "builtin-functions-and-types",
      children: "Builtin Functions and Types"
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["There are a number of builtin functions and builtin types in UPLC.\nThe list of builtin functions and types can be found in the ", (0,jsx_runtime.jsx)(_components.a, {
        href: "https://plutus.cardano.intersectmbo.org/resources/plutus-core-spec.pdf",
        children: "Plutus Core Specification"
      }), "."]
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["In ", (0,jsx_runtime.jsx)(_components.a, {
        href: "https://plutus.cardano.intersectmbo.org/haddock/latest/plutus-tx/PlutusTx-Builtins-Internal.html",
        children: (0,jsx_runtime.jsx)(_components.code, {
          children: "PlutusTx.Builtins.Internal"
        })
      }), ", functions marked ", (0,jsx_runtime.jsx)(_components.code, {
        children: "OPAQUE"
      }), " are directly converted to the corresponding builtin function.\nFor instance, ", (0,jsx_runtime.jsx)(_components.code, {
        children: "PlutusTx.Builtins.Internal.addInteger"
      }), " is converted to UPLC term ", (0,jsx_runtime.jsx)(_components.code, {
        children: "(builtin addInteger)"
      }), ".\nUsing the ", (0,jsx_runtime.jsx)(_components.code, {
        children: "OPAQUE"
      }), " pragma prevents GHC from inlining these functions, allowing the Plinth compiler to determine where exactly they are invoked, and compile them appropriately."]
    }), "\n", (0,jsx_runtime.jsx)(_components.p, {
      children: "Builtin types are handled similarly: rather than compiling their definition, they are directly converted to builtin types in PIR.\nIn UPLC, most types are erased, but constants remain tagged with the corresponding builtin types."
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["Since functions in ", (0,jsx_runtime.jsx)(_components.code, {
        children: "PlutusTx.Builtins.Internal"
      }), " correspond to builtin functions that operate on builtin types, it's usually preferable to use functions in ", (0,jsx_runtime.jsx)(_components.a, {
        href: "https://plutus.cardano.intersectmbo.org/haddock/latest/plutus-tx/PlutusTx-Builtins.html",
        children: (0,jsx_runtime.jsx)(_components.code, {
          children: "PlutusTx.Builtins"
        })
      }), ".\nThese functions wrap their counterparts in the ", (0,jsx_runtime.jsx)(_components.code, {
        children: "Internal"
      }), " module, and operate on standard Haskell types whenever possible, which are often more convenient."]
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["Aside from ", (0,jsx_runtime.jsx)(_components.code, {
        children: "BuiltinInteger"
      }), ", which is an alias for ", (0,jsx_runtime.jsx)(_components.code, {
        children: "Integer"
      }), ", other builtin types are distinct from their corresponding Haskell types.\nNot all of these Haskell types can be used in Plinth.\nFor instance, ", (0,jsx_runtime.jsx)(_components.code, {
        children: "String"
      }), " and ", (0,jsx_runtime.jsx)(_components.code, {
        children: "ByteString"
      }), " are not supported, whereas regular algebraic data types like ", (0,jsx_runtime.jsx)(_components.code, {
        children: "Bool"
      }), ", lists and pairs are supported."]
    }), "\n", (0,jsx_runtime.jsxs)(_components.h2, {
      id: "plutustxbool-and-plutustxbool",
      children: [(0,jsx_runtime.jsx)(_components.code, {
        children: "PlutusTx.Bool.&&"
      }), " and ", (0,jsx_runtime.jsx)(_components.code, {
        children: "PlutusTx.Bool.||"
      })]
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["In ", (0,jsx_runtime.jsx)(_components.a, {
        href: "https://plutus.cardano.intersectmbo.org/haddock/latest/plutus-tx/PlutusTx-Bool.html",
        children: (0,jsx_runtime.jsx)(_components.code, {
          children: "PlutusTx.Bool"
        })
      }), ", the ", (0,jsx_runtime.jsx)(_components.code, {
        children: "&&"
      }), " and ", (0,jsx_runtime.jsx)(_components.code, {
        children: "||"
      }), " operators are handled specially in the plugin to ensure they can short-circuit.\nIn most strict languages, these operators are special and cannot be defined by users, which is also the case for Plinth."]
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["Note that in regular Haskell, ", (0,jsx_runtime.jsx)(_components.code, {
        children: "&&"
      }), " and ", (0,jsx_runtime.jsx)(_components.code, {
        children: "||"
      }), " are ", (0,jsx_runtime.jsx)(_components.em, {
        children: "not"
      }), " special, as Haskell supports non-strict function applications (and it is the default behavior)."]
    }), "\n", (0,jsx_runtime.jsxs)(_components.h2, {
      id: "isstring-instances",
      children: [(0,jsx_runtime.jsx)(_components.code, {
        children: "IsString"
      }), " Instances"]
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: [(0,jsx_runtime.jsx)(_components.a, {
        href: "https://hackage.haskell.org/package/base/docs/Data-String.html#t:IsString",
        children: (0,jsx_runtime.jsx)(_components.code, {
          children: "IsString"
        })
      }), " is a type class from ", (0,jsx_runtime.jsx)(_components.code, {
        children: "base"
      }), ", and can be used along with the ", (0,jsx_runtime.jsx)(_components.code, {
        children: "OverloadedStrings"
      }), " language extension to convert string literals to types other than ", (0,jsx_runtime.jsx)(_components.code, {
        children: "String"
      }), "."]
    }), "\n", (0,jsx_runtime.jsxs)(_components.blockquote, {
      children: ["\n", (0,jsx_runtime.jsxs)(_components.p, {
        children: ["📌", " ", (0,jsx_runtime.jsx)(_components.strong, {
          children: "NOTE"
        })]
      }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
        children: [(0,jsx_runtime.jsx)(_components.code, {
          children: "String"
        }), " and ", (0,jsx_runtime.jsx)(_components.code, {
          children: "ByteString"
        }), " are not available in Plinth, so you'll need to use ", (0,jsx_runtime.jsx)(_components.code, {
          children: "BuiltinString"
        }), " or ", (0,jsx_runtime.jsx)(_components.code, {
          children: "BuiltinByteString"
        }), "."]
      }), "\n"]
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["This lets you write ", (0,jsx_runtime.jsx)(_components.code, {
        children: "\"hello\" :: BuiltinString"
      }), " in Plinth, which is quite convenient."]
    }), "\n", (0,jsx_runtime.jsx)(_components.h3, {
      id: "builtin-bytestring-literals",
      children: "Builtin ByteString literals"
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["Working with ", (0,jsx_runtime.jsx)(_components.code, {
        children: "BuiltinByteString"
      }), " using ", (0,jsx_runtime.jsx)(_components.code, {
        children: "OverloadedStrings"
      }), " requires care. For backward compatibility, an ", (0,jsx_runtime.jsx)(_components.code, {
        children: "IsString"
      }), " instance exists for ", (0,jsx_runtime.jsx)(_components.code, {
        children: "BuiltinByteString"
      }), ". This instance mirrors the standard Haskell ", (0,jsx_runtime.jsx)(_components.code, {
        children: "IsString ByteString"
      }), " behavior: it converts each character to a byte by taking the lowest 8 bits of its Unicode code point."]
    }), "\n", (0,jsx_runtime.jsx)(_components.p, {
      children: "However, its use is discouraged because this conversion is lossy, keeping only the lowest byte of each character's Unicode code point. This means that characters with Unicode code points above 255 (i.e., outside the Latin-1 range) will not be represented correctly, leading to potential data loss. The example below illustrates this truncation."
    }), "\n", (0,jsx_runtime.jsxs)(Details, {
      children: [(0,jsx_runtime.jsx)("summary", {
        children: "Example of lossy conversion"
      }), (0,jsx_runtime.jsx)(_components.pre, {
        children: (0,jsx_runtime.jsx)(_components.code, {
          className: "language-haskell",
          children: "{-# LANGUAGE OverloadedStrings #-}\n\nimport qualified Data.ByteString as BS\nimport Data.Char (ord)\nimport Data.Bits ((.&.))\n\nmain = do\n  print $ BS.unpack (\"世\" :: BS.ByteString)  -- [22]\n  print $ ord '世'                           -- 19990\n  print $ (19990 :: Integer) .&. 0xFF        -- 22 (truncation result)\n"
        })
      })]
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["Instead, Plinth provides encoding-specific newtypes, each with its own ", (0,jsx_runtime.jsx)(_components.code, {
        children: "IsString"
      }), " instance. Currently, two encodings are supported:"]
    }), "\n", (0,jsx_runtime.jsxs)(_components.ul, {
      children: ["\n", (0,jsx_runtime.jsxs)(_components.li, {
        children: [(0,jsx_runtime.jsx)(_components.strong, {
          children: "Hexadecimal"
        }), ", also known as ", (0,jsx_runtime.jsx)(_components.strong, {
          children: "Base 16"
        }), ", via the ", (0,jsx_runtime.jsx)(_components.code, {
          children: "BuiltinByteStringHex"
        }), " newtype."]
      }), "\n", (0,jsx_runtime.jsxs)(_components.li, {
        children: [(0,jsx_runtime.jsx)(_components.strong, {
          children: "UTF-8"
        }), " via the ", (0,jsx_runtime.jsx)(_components.code, {
          children: "BuiltinByteStringUtf8"
        }), " newtype."]
      }), "\n"]
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["The newtypes are zero-cost abstractions that tell the compiler which ", (0,jsx_runtime.jsx)(_components.code, {
        children: "IsString"
      }), " instance to use.\nThey can be converted to ", (0,jsx_runtime.jsx)(_components.code, {
        children: "BuiltinByteString"
      }), " using the corresponding functions:"]
    }), "\n", (0,jsx_runtime.jsx)(_components.pre, {
      children: (0,jsx_runtime.jsx)(_components.code, {
        className: "language-haskell",
        children: "unBuiltinByteStringHex :: BuiltinByteStringHex -> BuiltinByteString\nunBuiltinByteStringUtf8 :: BuiltinByteStringUtf8 -> BuiltinByteString\n"
      })
    }), "\n", (0,jsx_runtime.jsx)(_components.p, {
      children: "Here are some usage examples:"
    }), "\n", (0,jsx_runtime.jsx)(_components.pre, {
      children: (0,jsx_runtime.jsx)(_components.code, {
        className: "language-haskell",
        children: "{-# LANGUAGE OverloadedStrings #-}\n\nimport PlutusTx.Builtins \n  ( BuiltinByteString\n  , BuiltinByteStringUtf8\n  , unBuiltinByteStringHex\n  , unBuiltinByteStringUtf8\n  )\n\naceOfBase16 :: BuiltinByteString\naceOfBase16 = unBuiltinByteStringHex \"ACE0FBA5E\"\n-- ^ type inference figures out that the literal has \n-- the `BuiltinByteStringHex` type\n\nnonLatinTokenName :: BuiltinByteString\nnonLatinTokenName = \n  unBuiltinByteStringUtf8 \n    (\"Мой Клёвый Токен\" :: BuiltinByteStringUtf8)\n-- here we use an explicit ^^^ type annotation for the\n-- `BuiltinByteStringUtf8` newtype \n"
      })
    }), "\n", (0,jsx_runtime.jsxs)(_components.admonition, {
      type: "tip",
      children: [(0,jsx_runtime.jsxs)(_components.p, {
        children: ["You do not need to convert a ", (0,jsx_runtime.jsx)(_components.code, {
          children: "BuiltinByteStringHex"
        }), " or ", (0,jsx_runtime.jsx)(_components.code, {
          children: "BuiltinByteStringUtf8"
        }), " value to ", (0,jsx_runtime.jsx)(_components.code, {
          children: "BuiltinByteString"
        }), " immediately.\nYou can pass it around and only convert it when the context requires a ", (0,jsx_runtime.jsx)(_components.code, {
          children: "BuiltinByteString"
        }), ".\nThis preserves the encoding information in the type and allows downstream code to rule out invalid states.\nFor example:"]
      }), (0,jsx_runtime.jsx)(_components.pre, {
        children: (0,jsx_runtime.jsx)(_components.code, {
          className: "language-haskell",
          children: "hexBytes :: BuiltinByteStringHex\nhexBytes = \"AABBCCDD\" \n\nnumberOfBytes :: BuiltinByteStringHex -> Integer\nnumberOfBytes hex = lengthOfByteString (unBuiltinByteStringHex hex)\n"
        })
      })]
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["As an alternative to the ", (0,jsx_runtime.jsx)(_components.code, {
        children: "OverloadedStrings"
      }), " language extension, you can use special functions from the ", (0,jsx_runtime.jsx)(_components.code, {
        children: "PlutusTx.Builtins.HasOpaque"
      }), " module:"]
    }), "\n", (0,jsx_runtime.jsx)(_components.pre, {
      children: (0,jsx_runtime.jsx)(_components.code, {
        className: "language-haskell",
        children: "import PlutusTx.Builtins.HasOpaque \n  ( stringToBuiltinByteStringHex\n  , stringToBuiltinByteStringUtf8\n  )\n\n-- stringToBuiltinByteStringHex :: String -> BuiltinByteString\n\naceOfBase16 :: BuiltinByteString\naceOfBase16 = stringToBuiltinByteStringHex \"ACE0FBA5E\" \n\n-- stringToBuiltinByteStringUtf8 :: String -> BuiltinByteString\n\nmother :: BuiltinByteString\nmother = stringToBuiltinByteStringUtf8 \"Мама\"\n"
      })
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["These functions convert Haskell's ", (0,jsx_runtime.jsx)(_components.code, {
        children: "String"
      }), " literal to Plinth's ", (0,jsx_runtime.jsx)(_components.code, {
        children: "BuiltinByteString"
      }), " using the corresponding encoding.\nWhat makes them special is that they are executed by Plinth ", (0,jsx_runtime.jsx)(_components.strong, {
        children: "at compile time"
      }), ", without increasing the size and execution budget of a Plinth program."]
    }), "\n", (0,jsx_runtime.jsxs)(_components.admonition, {
      type: "caution",
      children: [(0,jsx_runtime.jsxs)(_components.p, {
        children: ["These compile-time functions need to be ", (0,jsx_runtime.jsx)(_components.em, {
          children: "syntactically"
        }), " applied to string literals, meaning that you cannot apply them to variables or expressions that are not string literals.\nFor example, the following code will not compile:"]
      }), (0,jsx_runtime.jsx)(_components.pre, {
        children: (0,jsx_runtime.jsx)(_components.code, {
          className: "language-haskell",
          children: "stringToBuiltinByteStringHex (\"ACE0F\" ++ \"BA5E\")\n"
        })
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