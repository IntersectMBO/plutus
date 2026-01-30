"use strict";
(self["webpackChunkdocusaurus"] = self["webpackChunkdocusaurus"] || []).push([[5222],{

/***/ 6868:
/***/ ((__unused_webpack_module, __webpack_exports__, __webpack_require__) => {

// ESM COMPAT FLAG
__webpack_require__.r(__webpack_exports__);

// EXPORTS
__webpack_require__.d(__webpack_exports__, {
  assets: () => (/* binding */ assets),
  contentTitle: () => (/* binding */ contentTitle),
  "default": () => (/* binding */ MDXContent),
  frontMatter: () => (/* binding */ frontMatter),
  metadata: () => (/* reexport */ site_docs_auction_smart_contract_end_to_end_placing_bids_md_bb0_namespaceObject),
  toc: () => (/* binding */ toc)
});

;// ./.docusaurus/docusaurus-plugin-content-docs/default/site-docs-auction-smart-contract-end-to-end-placing-bids-md-bb0.json
const site_docs_auction_smart_contract_end_to_end_placing_bids_md_bb0_namespaceObject = /*#__PURE__*/JSON.parse('{"id":"auction-smart-contract/end-to-end/placing-bids","title":"Placing Bids","description":"Now we can start bidding.","source":"@site/docs/auction-smart-contract/end-to-end/placing-bids.md","sourceDirName":"auction-smart-contract/end-to-end","slug":"/auction-smart-contract/end-to-end/placing-bids","permalink":"/pr-preview/docs/pr-7518/auction-smart-contract/end-to-end/placing-bids","draft":false,"unlisted":false,"editUrl":"https://github.com/IntersectMBO/plutus/edit/master/doc/docusaurus/docs/auction-smart-contract/end-to-end/placing-bids.md","tags":[],"version":"current","sidebarPosition":20,"frontMatter":{"sidebar_position":20},"sidebar":"tutorialSidebar","previous":{"title":"Minting the Token to be Auctioned","permalink":"/pr-preview/docs/pr-7518/auction-smart-contract/end-to-end/mint"},"next":{"title":"Closing the Auction","permalink":"/pr-preview/docs/pr-7518/auction-smart-contract/end-to-end/closing-the-auction"}}');
// EXTERNAL MODULE: ./node_modules/react/jsx-runtime.js
var jsx_runtime = __webpack_require__(4848);
// EXTERNAL MODULE: ./node_modules/@mdx-js/react/lib/index.js
var lib = __webpack_require__(8453);
;// ./docs/auction-smart-contract/end-to-end/placing-bids.md


const frontMatter = {
	sidebar_position: 20
};
const contentTitle = 'Placing Bids';

const assets = {

};



const toc = [];
function _createMdxContent(props) {
  const _components = {
    a: "a",
    code: "code",
    h1: "h1",
    h2: "h2",
    header: "header",
    hr: "hr",
    img: "img",
    li: "li",
    ol: "ol",
    p: "p",
    pre: "pre",
    section: "section",
    sup: "sup",
    ul: "ul",
    ...(0,lib/* useMDXComponents */.R)(),
    ...props.components
  }, {LiteralInclude} = _components;
  if (!LiteralInclude) _missingMdxReference("LiteralInclude", true);
  return (0,jsx_runtime.jsxs)(jsx_runtime.Fragment, {
    children: [(0,jsx_runtime.jsx)(_components.header, {
      children: (0,jsx_runtime.jsx)(_components.h1, {
        id: "placing-bids",
        children: "Placing Bids"
      })
    }), "\n", (0,jsx_runtime.jsx)(_components.p, {
      children: "Now we can start bidding.\nLet's place a bid of 100 Ada from bidder1, followed by a bid of 200 Ada from bidder2.\nEach transaction that places a bid must do the following:"
    }), "\n", (0,jsx_runtime.jsxs)(_components.ul, {
      children: ["\n", (0,jsx_runtime.jsxs)(_components.li, {
        children: ["Spend the UTxO that contains the token being auctioned.\nFor bidder1, the transaction that produced the UTxO is the one that minted the token.\nFor bidder2, the transaction that produced the UTxO is bidder1's transaction.\nThe address of this UTxO is always the auction validator's script address, so each bidding transaction must include the auction validator and a redeemer", (0,jsx_runtime.jsx)(_components.sup, {
          children: (0,jsx_runtime.jsx)(_components.a, {
            href: "#user-content-fn-1",
            id: "user-content-fnref-1",
            "data-footnote-ref": true,
            "aria-describedby": "footnote-label",
            children: "1"
          })
        }), "."]
      }), "\n", (0,jsx_runtime.jsxs)(_components.li, {
        children: ["Place a bid (via the redeemer) with an amount at least as high as the auction's minimum bid, and higher than the previous highest bid (if any).\nThe existence and the details of a previous highest bid can be determined by inspecting the datum attached to the aforementioned UTxO.\nThis is enforced by the auction validator's ", (0,jsx_runtime.jsx)(_components.code, {
          children: "sufficientBid"
        }), " condition."]
      }), "\n", (0,jsx_runtime.jsxs)(_components.li, {
        children: ["Lock the token being auctioned, together with the bid amount, in a new UTxO at the auction validator's script address.\nThe new UTxO should also include a datum containing the details of this bid.\nThis is enforced by the auction validator's ", (0,jsx_runtime.jsx)(_components.code, {
          children: "correctOutput"
        }), " condition."]
      }), "\n", (0,jsx_runtime.jsxs)(_components.li, {
        children: ["Refund the previous highest bid (if any) to its bidder's wallet address.\nThis is enforced by the auction validator's ", (0,jsx_runtime.jsx)(_components.code, {
          children: "refundsPreviousHighestBid"
        }), " condition."]
      }), "\n", (0,jsx_runtime.jsxs)(_components.li, {
        children: ["Set a validity interval that ends no later than the auction's end time.\nThis is enforced by the auction validator's ", (0,jsx_runtime.jsx)(_components.code, {
          children: "validBidTime"
        }), " condition."]
      }), "\n"]
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["To submit these bidding transactions, create a file named ", (0,jsx_runtime.jsx)(_components.code, {
        children: "off-chain/bid.mjs"
      }), " for the off-chain code, with the following content:"]
    }), "\n", (0,jsx_runtime.jsx)(LiteralInclude, {
      file: "bid.mjs",
      language: "javascript",
      title: "bid.mjs"
    }), "\n", (0,jsx_runtime.jsx)(_components.p, {
      children: "This Javascript module builds and submits a transaction that does exactly the above."
    }), "\n", (0,jsx_runtime.jsx)(_components.p, {
      children: "The following substitutions are needed:"
    }), "\n", (0,jsx_runtime.jsxs)(_components.ul, {
      children: ["\n", (0,jsx_runtime.jsxs)(_components.li, {
        children: ["Substitute your Blockfrost project ID for ", (0,jsx_runtime.jsx)(_components.code, {
          children: "Replace with Blockfrost Project ID"
        }), "."]
      }), "\n", (0,jsx_runtime.jsxs)(_components.li, {
        children: ["Substitute a slot number no later than the auction's end time for ", (0,jsx_runtime.jsx)(_components.code, {
          children: "Replace with transaction expiration time"
        }), ".\nFor instance, if you set the auction's end time to be approximately 24 hours from now, you can use a slot number corresponding to approximately 12 hours from now.\nTo determine the slot number, go to ", (0,jsx_runtime.jsx)(_components.a, {
          href: "https://preview.cardanoscan.io/",
          children: "Cardanoscan"
        }), ", click on a recent transaction, take its Absolute Slot, and add 12 hours (43200) to it."]
      }), "\n"]
    }), "\n", (0,jsx_runtime.jsx)(_components.p, {
      children: "Place the first bid by running"
    }), "\n", (0,jsx_runtime.jsx)(_components.pre, {
      children: (0,jsx_runtime.jsx)(_components.code, {
        children: "node bid.mjs <minting-transaction-hash> bidder1 100000000\n"
      })
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["Replace ", (0,jsx_runtime.jsx)(_components.code, {
        children: "<minting-transaction-hash>"
      }), " with the hash of the transaction we previously submitted for minting the token.\nThis hash is used by the off-chain code to locate the UTxO that contains the token."]
    }), "\n", (0,jsx_runtime.jsx)(_components.p, {
      children: "Illustration of the first bid:"
    }), "\n", (0,jsx_runtime.jsx)(_components.p, {
      children: (0,jsx_runtime.jsx)(_components.img, {
        alt: "First bid",
        src: (__webpack_require__(8676)/* ["default"] */ .A) + "",
        width: "1987",
        height: "1223"
      })
    }), "\n", (0,jsx_runtime.jsx)(_components.p, {
      children: "After the first bidding transaction is confirmed, we can submit the second bid from bidder2, with a similar command:"
    }), "\n", (0,jsx_runtime.jsx)(_components.pre, {
      children: (0,jsx_runtime.jsx)(_components.code, {
        children: "node bid.mjs <bidder1-transaction-hash> bidder2 200000000\n"
      })
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["Replace ", (0,jsx_runtime.jsx)(_components.code, {
        children: "<bidder1-transaction-hash>"
      }), " with the hash of the previous transaction."]
    }), "\n", (0,jsx_runtime.jsx)(_components.p, {
      children: "Illustration of the second bid:"
    }), "\n", (0,jsx_runtime.jsx)(_components.p, {
      children: (0,jsx_runtime.jsx)(_components.img, {
        alt: "Second bid",
        src: (__webpack_require__(2573)/* ["default"] */ .A) + "",
        width: "1987",
        height: "1223"
      })
    }), "\n", (0,jsx_runtime.jsx)(_components.hr, {}), "\n", "\n", (0,jsx_runtime.jsxs)(_components.section, {
      "data-footnotes": true,
      className: "footnotes",
      children: [(0,jsx_runtime.jsx)(_components.h2, {
        className: "sr-only",
        id: "footnote-label",
        children: "Footnotes"
      }), "\n", (0,jsx_runtime.jsxs)(_components.ol, {
        children: ["\n", (0,jsx_runtime.jsxs)(_components.li, {
          id: "user-content-fn-1",
          children: ["\n", (0,jsx_runtime.jsxs)(_components.p, {
            children: ["Instead of including the script in the transaction, we can use a reference script, but to keep things simple, we won't discuss that here. ", (0,jsx_runtime.jsx)(_components.a, {
              href: "#user-content-fnref-1",
              "data-footnote-backref": "",
              "aria-label": "Back to reference 1",
              className: "data-footnote-backref",
              children: "↩"
            })]
          }), "\n"]
        }), "\n"]
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
function _missingMdxReference(id, component) {
  throw new Error("Expected " + (component ? "component" : "object") + " `" + id + "` to be defined: you likely forgot to import, pass, or provide it.");
}



/***/ }),

/***/ 8676:
/***/ ((__unused_webpack_module, __webpack_exports__, __webpack_require__) => {

/* harmony export */ __webpack_require__.d(__webpack_exports__, {
/* harmony export */   A: () => (__WEBPACK_DEFAULT_EXPORT__)
/* harmony export */ });
/* harmony default export */ const __WEBPACK_DEFAULT_EXPORT__ = (__webpack_require__.p + "assets/images/tx2-7cb7b23b48acce462e98ea0fa40b7c2d.png");

/***/ }),

/***/ 2573:
/***/ ((__unused_webpack_module, __webpack_exports__, __webpack_require__) => {

/* harmony export */ __webpack_require__.d(__webpack_exports__, {
/* harmony export */   A: () => (__WEBPACK_DEFAULT_EXPORT__)
/* harmony export */ });
/* harmony default export */ const __WEBPACK_DEFAULT_EXPORT__ = (__webpack_require__.p + "assets/images/tx3-7a43611c9c58e1fb25031ddb2feb9248.png");

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