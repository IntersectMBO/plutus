"use strict";
(self["webpackChunkdocusaurus"] = self["webpackChunkdocusaurus"] || []).push([[4180],{

/***/ 709:
/***/ ((__unused_webpack_module, __webpack_exports__, __webpack_require__) => {

// ESM COMPAT FLAG
__webpack_require__.r(__webpack_exports__);

// EXPORTS
__webpack_require__.d(__webpack_exports__, {
  assets: () => (/* binding */ assets),
  contentTitle: () => (/* binding */ contentTitle),
  "default": () => (/* binding */ MDXContent),
  frontMatter: () => (/* binding */ frontMatter),
  metadata: () => (/* reexport */ site_docs_auction_smart_contract_end_to_end_mint_md_4e0_namespaceObject),
  toc: () => (/* binding */ toc)
});

;// ./.docusaurus/docusaurus-plugin-content-docs/default/site-docs-auction-smart-contract-end-to-end-mint-md-4e0.json
const site_docs_auction_smart_contract_end_to_end_mint_md_4e0_namespaceObject = /*#__PURE__*/JSON.parse('{"id":"auction-smart-contract/end-to-end/mint","title":"Minting the Token to be Auctioned","description":"Before we can start the auction, we need to mint a token to be auctioned.","source":"@site/docs/auction-smart-contract/end-to-end/mint.md","sourceDirName":"auction-smart-contract/end-to-end","slug":"/auction-smart-contract/end-to-end/mint","permalink":"/pr-preview/docs/pr-7544/auction-smart-contract/end-to-end/mint","draft":false,"unlisted":false,"editUrl":"https://github.com/IntersectMBO/plutus/edit/master/doc/docusaurus/docs/auction-smart-contract/end-to-end/mint.md","tags":[],"version":"current","sidebarPosition":15,"frontMatter":{"sidebar_position":15},"sidebar":"tutorialSidebar","previous":{"title":"Getting Funds from the Faucet","permalink":"/pr-preview/docs/pr-7544/auction-smart-contract/end-to-end/getting-funds"},"next":{"title":"Placing Bids","permalink":"/pr-preview/docs/pr-7544/auction-smart-contract/end-to-end/placing-bids"}}');
// EXTERNAL MODULE: ./node_modules/react/jsx-runtime.js
var jsx_runtime = __webpack_require__(4848);
// EXTERNAL MODULE: ./node_modules/@mdx-js/react/lib/index.js
var lib = __webpack_require__(8453);
;// ./docs/auction-smart-contract/end-to-end/mint.md


const frontMatter = {
	sidebar_position: 15
};
const contentTitle = 'Minting the Token to be Auctioned';

const assets = {

};



const toc = [{
  "value": "On-chain Minting Policy Script",
  "id": "on-chain-minting-policy-script",
  "level": 2
}, {
  "value": "Compile and Generate Blueprint for the Minting Policy",
  "id": "compile-and-generate-blueprint-for-the-minting-policy",
  "level": 2
}, {
  "value": "Compile and Generate Blueprint for the Auction Validator",
  "id": "compile-and-generate-blueprint-for-the-auction-validator",
  "level": 2
}, {
  "value": "Off-chain Code for Minting",
  "id": "off-chain-code-for-minting",
  "level": 2
}];
function _createMdxContent(props) {
  const _components = {
    a: "a",
    blockquote: "blockquote",
    code: "code",
    em: "em",
    h1: "h1",
    h2: "h2",
    header: "header",
    img: "img",
    li: "li",
    ol: "ol",
    p: "p",
    pre: "pre",
    strong: "strong",
    ul: "ul",
    ...(0,lib/* useMDXComponents */.R)(),
    ...props.components
  }, {LiteralInclude} = _components;
  if (!LiteralInclude) _missingMdxReference("LiteralInclude", true);
  return (0,jsx_runtime.jsxs)(jsx_runtime.Fragment, {
    children: [(0,jsx_runtime.jsx)(_components.header, {
      children: (0,jsx_runtime.jsx)(_components.h1, {
        id: "minting-the-token-to-be-auctioned",
        children: "Minting the Token to be Auctioned"
      })
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["Before we can start the auction, we need to mint a token to be auctioned.\nTo do so, we first must determine the token's currency symbol and name.\nTo mint or burn tokens with a specific currency symbol (", (0,jsx_runtime.jsx)(_components.code, {
        children: "currencySymbol"
      }), "), a Plutus script whose hash matches ", (0,jsx_runtime.jsx)(_components.code, {
        children: "currencySymbol"
      }), " must be provided, and is used to validate the minting or burning action.\nTherefore, we'll first write the on-chain script, then compute its hash and use it as the currency symbol."]
    }), "\n", (0,jsx_runtime.jsx)(_components.h2, {
      id: "on-chain-minting-policy-script",
      children: "On-chain Minting Policy Script"
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["The full minting policy code can be found at ", (0,jsx_runtime.jsx)(_components.a, {
        href: "https://github.com/IntersectMBO/plinth-template/blob/main/src/AuctionMintingPolicy.hs",
        children: "AuctionMintingPolicy.hs"
      }), ".\nThe main logic is in the following function:"]
    }), "\n", (0,jsx_runtime.jsx)(LiteralInclude, {
      file: "AuctionMintingPolicy.hs",
      language: "haskell",
      title: "AuctionMintingPolicy.hs",
      start: "-- BLOCK1",
      end: "-- BLOCK2"
    }), "\n", (0,jsx_runtime.jsx)(_components.p, {
      children: "This script will pass if the following two conditions are met:"
    }), "\n", (0,jsx_runtime.jsxs)(_components.ol, {
      children: ["\n", (0,jsx_runtime.jsx)(_components.li, {
        children: "The transaction is signed by a specific public key."
      }), "\n", (0,jsx_runtime.jsxs)(_components.li, {
        children: ["The transaction mints exactly one token, whose currency symbol matches the script's hash (i.e., ", (0,jsx_runtime.jsx)(_components.code, {
          children: "ownCurrencySymbol ctx"
        }), ").\nThe token name can be anything."]
      }), "\n"]
    }), "\n", (0,jsx_runtime.jsxs)(_components.blockquote, {
      children: ["\n", (0,jsx_runtime.jsxs)(_components.p, {
        children: ["📌", " ", (0,jsx_runtime.jsx)(_components.strong, {
          children: "NOTE"
        })]
      }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
        children: ["A token minted in this way is ", (0,jsx_runtime.jsx)(_components.em, {
          children: "not"
        }), " considered a non-fungible token (NFT) because, while only one token can be minted in a single transaction, multiple transactions can mint additional tokens with the same currency symbol and token name.\nTo create a truly unique token, you would need a more complex minting policy, but for simplicity, that is not covered here."]
      }), "\n"]
    }), "\n", (0,jsx_runtime.jsx)(_components.h2, {
      id: "compile-and-generate-blueprint-for-the-minting-policy",
      children: "Compile and Generate Blueprint for the Minting Policy"
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["Next, we need to compile the minting policy script and create its blueprint.\nTo do so, we first need to supply a public key hash, which the minting policy will use for checking condition 1 above.\nAssuming the seller is the one minting the token, this should be the seller's public key hash.\nOpen ", (0,jsx_runtime.jsx)(_components.code, {
        children: "GenMintingPolicyBlueprint.hs"
      }), " in the ", (0,jsx_runtime.jsx)(_components.code, {
        children: "on-chain"
      }), " directory, and replace ", (0,jsx_runtime.jsx)(_components.code, {
        children: "error \"Replace with seller pkh\""
      }), " with the content of ", (0,jsx_runtime.jsx)(_components.code, {
        children: "off-chain/seller.pkh"
      }), "."]
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["The minting policy code comes with ", (0,jsx_runtime.jsx)(_components.code, {
        children: "plinth-template"
      }), ", so you can find it in the ", (0,jsx_runtime.jsx)(_components.code, {
        children: "on-chain"
      }), " repository.\nTo compile it and generate the blueprint, navigate to the ", (0,jsx_runtime.jsx)(_components.code, {
        children: "on-chain"
      }), " directory and run"]
    }), "\n", (0,jsx_runtime.jsx)(_components.pre, {
      children: (0,jsx_runtime.jsx)(_components.code, {
        children: "cabal run gen-minting-policy-blueprint -- ../off-chain/plutus-auction-minting-policy.json\n"
      })
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["You may need to run ", (0,jsx_runtime.jsx)(_components.code, {
        children: "cabal update"
      }), " before executing this command for the first time."]
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["This should produce a blueprint file named ", (0,jsx_runtime.jsx)(_components.code, {
        children: "off-chain/plutus-auction-minting-policy.json"
      }), "."]
    }), "\n", (0,jsx_runtime.jsx)(_components.h2, {
      id: "compile-and-generate-blueprint-for-the-auction-validator",
      children: "Compile and Generate Blueprint for the Auction Validator"
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["One final step before minting the token: since we want to lock the minted token at the script address corresponding to the auction validator,\nwe must supply the parameters (i.e., ", (0,jsx_runtime.jsx)(_components.code, {
        children: "AuctionParams"
      }), ") to the auction validator, compile the auction validator, and calculate its script address."]
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["Open ", (0,jsx_runtime.jsx)(_components.code, {
        children: "GenAuctionValidatorBlueprint.hs"
      }), " in the ", (0,jsx_runtime.jsx)(_components.code, {
        children: "on-chain"
      }), " directory, and replace all placeholders:"]
    }), "\n", (0,jsx_runtime.jsxs)(_components.ul, {
      children: ["\n", (0,jsx_runtime.jsxs)(_components.li, {
        children: ["Replace the ", (0,jsx_runtime.jsx)(_components.code, {
          children: "apSeller"
        }), " value with the content of ", (0,jsx_runtime.jsx)(_components.code, {
          children: "off-chain/seller.pkh"
        }), "."]
      }), "\n", (0,jsx_runtime.jsxs)(_components.li, {
        children: ["Replace the ", (0,jsx_runtime.jsx)(_components.code, {
          children: "apCurrencySymbol"
        }), " value with the minting policy hash, which you can find in the ", (0,jsx_runtime.jsx)(_components.code, {
          children: "hash"
        }), " field in ", (0,jsx_runtime.jsx)(_components.code, {
          children: "off-chain/plutus-auction-minting-policy.json"
        }), "."]
      }), "\n", (0,jsx_runtime.jsxs)(_components.li, {
        children: ["Replace the ", (0,jsx_runtime.jsx)(_components.code, {
          children: "apEndTime"
        }), " value with a POSIX timestamp for a time in the near future (say 24 hours from now).\nNote that the POSIX timestamp in Plutus is the number of ", (0,jsx_runtime.jsx)(_components.em, {
          children: "milliseconds"
        }), ", rather than seconds, elapsed since January 1, 1970.\nIn other words, add three zeros to the usual POSIX timestamp.\nFor instance, the POSIX timestamp of September 1, 2024, 21:44:51 UTC, is 1725227091000."]
      }), "\n"]
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["Then, navigate to the ", (0,jsx_runtime.jsx)(_components.code, {
        children: "on-chain"
      }), " directory and run"]
    }), "\n", (0,jsx_runtime.jsx)(_components.pre, {
      children: (0,jsx_runtime.jsx)(_components.code, {
        children: "cabal run gen-auction-validator-blueprint -- ../off-chain/plutus-auction-validator.json\n"
      })
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["This will generate a blueprint file named ", (0,jsx_runtime.jsx)(_components.code, {
        children: "off-chain/plutus-auction-validator.json"
      }), ", which the off-chain code can read and calculate the auction validator's script address."]
    }), "\n", (0,jsx_runtime.jsx)(_components.h2, {
      id: "off-chain-code-for-minting",
      children: "Off-chain Code for Minting"
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["We are now ready to write and execute the off-chain code for minting.\nCreate a file named ", (0,jsx_runtime.jsx)(_components.code, {
        children: "off-chain/mint-token-for-auction.mjs"
      }), " with the following content:"]
    }), "\n", (0,jsx_runtime.jsx)(LiteralInclude, {
      file: "mint-token-for-auction.mjs",
      language: "javascript",
      title: "mint-token-for-auction.mjs"
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["Substitute your Blockfrost project ID for ", (0,jsx_runtime.jsx)(_components.code, {
        children: "Replace with Blockfrost Project ID"
      }), "."]
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["This Javascript module uses the mesh library to build a transaction that mints a token (", (0,jsx_runtime.jsx)(_components.code, {
        children: "tx.mintAsset"
      }), ").\nThe token will have the currency symbol of the minting policy's hash, and a token name of ", (0,jsx_runtime.jsx)(_components.code, {
        children: "TokenToBeAuctioned"
      }), ".\nIt will be sent to ", (0,jsx_runtime.jsx)(_components.code, {
        children: "auctionValidatorAddress"
      }), ", with a datum corresponding to ", (0,jsx_runtime.jsx)(_components.code, {
        children: "Nothing"
      }), ".\nThe transaction is signed by the seller (", (0,jsx_runtime.jsx)(_components.code, {
        children: "seller.skey"
      }), "), and then submitted to the Preview testnet."]
    }), "\n", (0,jsx_runtime.jsx)(_components.p, {
      children: "Run the coding using:"
    }), "\n", (0,jsx_runtime.jsx)(_components.pre, {
      children: (0,jsx_runtime.jsx)(_components.code, {
        children: "node mint-token-for-auction.mjs\n"
      })
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["and you should see a message \"Minted a token at address ...\" printed in the console.\nWithin a minute, you should be able to find the transaction using the transaction hash on ", (0,jsx_runtime.jsx)(_components.a, {
        href: "https://preview.cardanoscan.io/",
        children: "Cardanoscan"
      }), " and review its details."]
    }), "\n", (0,jsx_runtime.jsx)(_components.p, {
      children: "Illustration of the minting transaction:"
    }), "\n", (0,jsx_runtime.jsx)(_components.p, {
      children: (0,jsx_runtime.jsx)(_components.img, {
        alt: "Minting the token",
        src: (__webpack_require__(5535)/* ["default"] */ .A) + "",
        width: "1987",
        height: "1223"
      })
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

/***/ 5535:
/***/ ((__unused_webpack_module, __webpack_exports__, __webpack_require__) => {

/* harmony export */ __webpack_require__.d(__webpack_exports__, {
/* harmony export */   A: () => (__WEBPACK_DEFAULT_EXPORT__)
/* harmony export */ });
/* harmony default export */ const __WEBPACK_DEFAULT_EXPORT__ = (__webpack_require__.p + "assets/images/tx1-e6b6398e9a89b21bb14fec62ac2b9787.png");

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