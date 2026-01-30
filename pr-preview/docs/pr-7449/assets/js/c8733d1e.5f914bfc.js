"use strict";
(self["webpackChunkdocusaurus"] = self["webpackChunkdocusaurus"] || []).push([[135],{

/***/ 2164:
/***/ ((__unused_webpack_module, __webpack_exports__, __webpack_require__) => {

// ESM COMPAT FLAG
__webpack_require__.r(__webpack_exports__);

// EXPORTS
__webpack_require__.d(__webpack_exports__, {
  assets: () => (/* binding */ assets),
  contentTitle: () => (/* binding */ contentTitle),
  "default": () => (/* binding */ MDXContent),
  frontMatter: () => (/* binding */ frontMatter),
  metadata: () => (/* reexport */ site_docs_auction_smart_contract_on_chain_code_md_c87_namespaceObject),
  toc: () => (/* binding */ toc)
});

;// ./.docusaurus/docusaurus-plugin-content-docs/default/site-docs-auction-smart-contract-on-chain-code-md-c87.json
const site_docs_auction_smart_contract_on_chain_code_md_c87_namespaceObject = /*#__PURE__*/JSON.parse('{"id":"auction-smart-contract/on-chain-code","title":"On-chain Code: The Auction Validator","description":"The code in this example is not a production-ready implementation, as it is not optimized for security or efficiency.","source":"@site/docs/auction-smart-contract/on-chain-code.md","sourceDirName":"auction-smart-contract","slug":"/auction-smart-contract/on-chain-code","permalink":"/pr-preview/docs/pr-7449/auction-smart-contract/on-chain-code","draft":false,"unlisted":false,"editUrl":"https://github.com/IntersectMBO/plutus/edit/master/doc/docusaurus/docs/auction-smart-contract/on-chain-code.md","tags":[],"version":"current","sidebarPosition":5,"frontMatter":{"sidebar_position":5},"sidebar":"tutorialSidebar","previous":{"title":"Example: An Auction Smart Contract","permalink":"/pr-preview/docs/pr-7449/category/example-an-auction-smart-contract"},"next":{"title":"End to end","permalink":"/pr-preview/docs/pr-7449/category/end-to-end"}}');
// EXTERNAL MODULE: ./node_modules/react/jsx-runtime.js
var jsx_runtime = __webpack_require__(4848);
// EXTERNAL MODULE: ./node_modules/@mdx-js/react/lib/index.js
var lib = __webpack_require__(8453);
;// ./docs/auction-smart-contract/on-chain-code.md


const frontMatter = {
	sidebar_position: 5
};
const contentTitle = 'On-chain Code: The Auction Validator';

const assets = {

};



const toc = [{
  "value": "Data types",
  "id": "data-types",
  "level": 2
}, {
  "value": "1. Contract parameters",
  "id": "1-contract-parameters",
  "level": 3
}, {
  "value": "2. Datum",
  "id": "2-datum",
  "level": 3
}, {
  "value": "3. Redeemer",
  "id": "3-redeemer",
  "level": 3
}, {
  "value": "4. Script context",
  "id": "4-script-context",
  "level": 3
}, {
  "value": "Main Validator Function",
  "id": "main-validator-function",
  "level": 2
}, {
  "value": "Sufficient Bid Condition",
  "id": "sufficient-bid-condition",
  "level": 3
}, {
  "value": "Valid Bid Time Condition",
  "id": "valid-bid-time-condition",
  "level": 3
}, {
  "value": "Refunds Previous Highest Bid Condition",
  "id": "refunds-previous-highest-bid-condition",
  "level": 3
}, {
  "value": "Correct Output Condition",
  "id": "correct-output-condition",
  "level": 3
}, {
  "value": "Compiling the validator",
  "id": "compiling-the-validator",
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
    strong: "strong",
    ul: "ul",
    ...(0,lib/* useMDXComponents */.R)(),
    ...props.components
  }, {LiteralInclude} = _components;
  if (!LiteralInclude) _missingMdxReference("LiteralInclude", true);
  return (0,jsx_runtime.jsxs)(jsx_runtime.Fragment, {
    children: [(0,jsx_runtime.jsx)(_components.header, {
      children: (0,jsx_runtime.jsx)(_components.h1, {
        id: "on-chain-code-the-auction-validator",
        children: "On-chain Code: The Auction Validator"
      })
    }), "\n", (0,jsx_runtime.jsx)(_components.admonition, {
      type: "caution",
      children: (0,jsx_runtime.jsxs)(_components.p, {
        children: ["The code in this example is not a production-ready implementation, as it is not optimized for security or efficiency.\nIt is provided purely as an example for illustration and educational purposes.\nRefer to resources like ", (0,jsx_runtime.jsx)(_components.strong, {
          children: (0,jsx_runtime.jsx)(_components.a, {
            href: "https://library.mlabs.city/common-plutus-security-vulnerabilities",
            children: "Cardano Plutus Script Vulnerability Guide"
          })
        }), " for best practices on developing secure smart contracts."]
      })
    }), "\n", (0,jsx_runtime.jsx)(_components.h1, {
      id: "auction-properties",
      children: "Auction Properties"
    }), "\n", (0,jsx_runtime.jsx)(_components.p, {
      children: "In this example, a seller wants to auction some asset she owns, represented as a non-fungible token (NFT) on Cardano.\nShe would like to create and deploy an auction smart contract with the following properties:"
    }), "\n", (0,jsx_runtime.jsxs)(_components.ul, {
      children: ["\n", (0,jsx_runtime.jsx)(_components.li, {
        children: "there is a minimum bid amount"
      }), "\n", (0,jsx_runtime.jsx)(_components.li, {
        children: "each bid must be higher than the previous highest bid (if any)"
      }), "\n", (0,jsx_runtime.jsx)(_components.li, {
        children: "once a new bid is made, the previous highest bid (if exists) is immediately refunded"
      }), "\n", (0,jsx_runtime.jsx)(_components.li, {
        children: "there is a deadline for placing bids; once the deadline has passed, new bids are no longer accepted, the asset can be transferred to the highest bidder (or to the seller if there are no bids), and the highest bid (if exists) can be transferred to the seller."
      }), "\n"]
    }), "\n", (0,jsx_runtime.jsx)(_components.h1, {
      id: "plinth-code",
      children: "Plinth Code"
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["Plinth is a subset of Haskell, used to write on-chain code, also known as validators or scripts.\nA Plinth program is compiled into Plutus Core, which is interpreted on-chain.\nThe full Plinth code for the auction smart contract can be found at ", (0,jsx_runtime.jsx)(_components.a, {
        href: "https://github.com/IntersectMBO/plinth-template/blob/main/src/AuctionValidator.hs",
        children: "AuctionValidator.hs"
      }), "."]
    }), "\n", (0,jsx_runtime.jsx)(_components.h2, {
      id: "data-types",
      children: "Data types"
    }), "\n", (0,jsx_runtime.jsx)(_components.p, {
      children: "First, let's define the following data types and instances for the validator:"
    }), "\n", (0,jsx_runtime.jsx)(LiteralInclude, {
      file: "AuctionValidator.hs",
      language: "haskell",
      title: "Data types",
      start: "-- BLOCK1",
      end: "-- BLOCK2"
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["The purpose of ", (0,jsx_runtime.jsx)(_components.code, {
        children: "makeLift"
      }), " and ", (0,jsx_runtime.jsx)(_components.code, {
        children: "makeIsDataSchemaIndexed"
      }), " will be explained later."]
    }), "\n", (0,jsx_runtime.jsx)(_components.p, {
      children: "Writing a Plinth validator script for a smart contract often involves the following data types:"
    }), "\n", (0,jsx_runtime.jsx)(_components.h3, {
      id: "1-contract-parameters",
      children: "1. Contract parameters"
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["These are fixed properties of the contract. You can put here values that will never change during the contract's life cycle.\nIn our example, it is the ", (0,jsx_runtime.jsx)(_components.code, {
        children: "AuctionParams"
      }), " type, containing properties like seller and minimum bid."]
    }), "\n", (0,jsx_runtime.jsx)(_components.h3, {
      id: "2-datum",
      children: "2. Datum"
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["This is part of a script UTXO.\nIt's commonly used to hold the state of the contract and values that can change throughout the contract's life cycle.\nOur example requires only one piece of state: the current highest bid.\nWe use the ", (0,jsx_runtime.jsx)(_components.code, {
        children: "AuctionDatum"
      }), " type to represent this."]
    }), "\n", (0,jsx_runtime.jsx)(_components.h3, {
      id: "3-redeemer",
      children: "3. Redeemer"
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["This is an input to the Plutus script provided by the transaction that is trying to spend a script UTXO.\nIf a smart contract is regarded as a state machine, the redeemer would be the input that ticks the state machine.\nIn our example, it is the ", (0,jsx_runtime.jsx)(_components.code, {
        children: "AuctionRedeemer"
      }), " type: one may either submit a new bid, or request to close the auction and pay out the winner and the seller, both of which lead to a new state of the auction."]
    }), "\n", (0,jsx_runtime.jsx)(_components.h3, {
      id: "4-script-context",
      children: "4. Script context"
    }), "\n", (0,jsx_runtime.jsx)(_components.p, {
      children: "This type contains the information of the transaction that the validator can inspect.\nIn our example, our validator verifies several conditions of the transaction; e.g., if it is a new bid, then it must be submitted before the auction's end time; the previous highest bid must be refunded to the previous bidder, etc."
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["Different ", (0,jsx_runtime.jsx)(_components.a, {
        href: "/pr-preview/docs/pr-7449/working-with-scripts/ledger-language-version",
        children: "ledger language versions"
      }), " use different script context types.\nIn this example we are writing a Plutus V3 scripts, so we import the ", (0,jsx_runtime.jsx)(_components.code, {
        children: "ScriptContext"
      }), " data type from ", (0,jsx_runtime.jsx)(_components.code, {
        children: "PlutusLedgerApi.V3.Contexts"
      }), "."]
    }), "\n", (0,jsx_runtime.jsxs)(_components.blockquote, {
      children: ["\n", (0,jsx_runtime.jsxs)(_components.p, {
        children: ["📌", " ", (0,jsx_runtime.jsx)(_components.strong, {
          children: "NOTE"
        })]
      }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
        children: ["When writing a Plutus validator using Plinth, it is advisable to turn off Haskell's ", (0,jsx_runtime.jsx)(_components.code, {
          children: "Prelude"
        }), ". One way of doing it is the GHC extension ", (0,jsx_runtime.jsx)(_components.code, {
          children: "NoImplicitPrelude"
        }), " enabled in the module header.\nUsage of most functions and methods in ", (0,jsx_runtime.jsx)(_components.code, {
          children: "Prelude"
        }), " should be replaced by their counterparts in the ", (0,jsx_runtime.jsx)(_components.code, {
          children: "plutus-tx"
        }), " library, e.g., instead of the ", (0,jsx_runtime.jsx)(_components.code, {
          children: "=="
        }), " from ", (0,jsx_runtime.jsx)(_components.code, {
          children: "base"
        }), ", use ", (0,jsx_runtime.jsx)(_components.code, {
          children: "PlutusTx.Eq.=="
        }), "."]
      }), "\n"]
    }), "\n", (0,jsx_runtime.jsx)(_components.h2, {
      id: "main-validator-function",
      children: "Main Validator Function"
    }), "\n", (0,jsx_runtime.jsx)(_components.p, {
      children: "Now we are ready to introduce our main validator function.\nThe beginning of the function looks like the following:"
    }), "\n", (0,jsx_runtime.jsx)(LiteralInclude, {
      file: "AuctionValidator.hs",
      language: "haskell",
      title: "Main validator function",
      start: "-- BLOCK2",
      end: "-- BLOCK3"
    }), "\n", (0,jsx_runtime.jsx)(_components.p, {
      children: "Depending on whether this transaction is attempting to submit a new bid or to request payout, the validator validates the corresponding set of conditions."
    }), "\n", (0,jsx_runtime.jsx)(_components.h3, {
      id: "sufficient-bid-condition",
      children: "Sufficient Bid Condition"
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["The ", (0,jsx_runtime.jsx)(_components.code, {
        children: "sufficientBid"
      }), " condition verifies that the bid amount is sufficient:"]
    }), "\n", (0,jsx_runtime.jsx)(LiteralInclude, {
      file: "AuctionValidator.hs",
      language: "haskell",
      title: "Sufficient bid condition",
      start: "-- BLOCK3",
      end: "-- BLOCK4"
    }), "\n", (0,jsx_runtime.jsx)(_components.h3, {
      id: "valid-bid-time-condition",
      children: "Valid Bid Time Condition"
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["The ", (0,jsx_runtime.jsx)(_components.code, {
        children: "validBidTime"
      }), " condition verifies that the bid is submitted before the auction's deadline:"]
    }), "\n", (0,jsx_runtime.jsx)(LiteralInclude, {
      file: "AuctionValidator.hs",
      language: "haskell",
      title: "Valid bid time condition",
      start: "-- BLOCK4",
      end: "-- BLOCK5"
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["Here, ", (0,jsx_runtime.jsx)(_components.code, {
        children: "to x"
      }), " is the time interval ending at ", (0,jsx_runtime.jsx)(_components.code, {
        children: "x"
      }), ", i.e., ", (0,jsx_runtime.jsx)(_components.code, {
        children: "(-∞, x]"
      }), ".\n", (0,jsx_runtime.jsx)(_components.code, {
        children: "txInfoValidRange"
      }), " is a transaction property.\nIt is the time interval in which the transaction is allowed to go through phase-1 validation.\n", (0,jsx_runtime.jsx)(_components.code, {
        children: "contains"
      }), " takes two time intervals, and checks that the first interval completely includes the second.\nSince the transaction may be validated at any point in the ", (0,jsx_runtime.jsx)(_components.code, {
        children: "txInfoValidRange"
      }), " interval, we need to check that the entire interval lies within ", (0,jsx_runtime.jsx)(_components.code, {
        children: "(-∞, apEndTime params]"
      }), "."]
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["The reason a script receives the ", (0,jsx_runtime.jsx)(_components.code, {
        children: "txInfoValidRange"
      }), " interval instead of the exact time the script is run is due to ", (0,jsx_runtime.jsx)(_components.a, {
        href: "https://iohk.io/en/blog/posts/2021/09/06/no-surprises-transaction-validation-on-cardano/",
        children: "determinism"
      }), ".\nUsing the exact time would be like calling a ", (0,jsx_runtime.jsx)(_components.code, {
        children: "getCurrentTime"
      }), " function and branching based on the current time.\nOn the other hand, by using the ", (0,jsx_runtime.jsx)(_components.code, {
        children: "txInfoValidRange"
      }), " interval, the same interval is always used by the same transaction.\nIf the current time when the transaction is validated is outside of the interval, the transaction is rejected immediately without running the script."]
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["Also note the tilde (", (0,jsx_runtime.jsx)(_components.code, {
        children: "~"
      }), ") in ", (0,jsx_runtime.jsx)(_components.code, {
        children: "~validBidTime = ..."
      }), ".\nWhen writing Plinth it is ", (0,jsx_runtime.jsx)(_components.a, {
        href: "/pr-preview/docs/pr-7449/using-plinth/compiling-plinth",
        children: "advisable"
      }), " to turn on the ", (0,jsx_runtime.jsx)(_components.code, {
        children: "Strict"
      }), " extension, which generally improves script performance.\nDoing so makes all bindings strict, which means, in this particular case, without the ", (0,jsx_runtime.jsx)(_components.code, {
        children: "~"
      }), ", ", (0,jsx_runtime.jsx)(_components.code, {
        children: "validBidTime"
      }), " would be evaluated even if the redeemer matches the ", (0,jsx_runtime.jsx)(_components.code, {
        children: "Payout"
      }), " case, which doesn't need this condition.\nDoing so results in unnecessary work or even unexpected evaluation failures.\nThe ", (0,jsx_runtime.jsx)(_components.code, {
        children: "~"
      }), " makes ", (0,jsx_runtime.jsx)(_components.code, {
        children: "validBidTime"
      }), " non-strict, i.e., only evaluated when used."]
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["On the other hand, it is unnecessary to add ", (0,jsx_runtime.jsx)(_components.code, {
        children: "~"
      }), " to ", (0,jsx_runtime.jsx)(_components.code, {
        children: "sufficientBid"
      }), ", since it has a function type, and a function cannot be evaluated further without receiving enough arguments."]
    }), "\n", (0,jsx_runtime.jsx)(_components.h3, {
      id: "refunds-previous-highest-bid-condition",
      children: "Refunds Previous Highest Bid Condition"
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["The ", (0,jsx_runtime.jsx)(_components.code, {
        children: "refundsPreviousHighestBid"
      }), " condition checks that the transaction pays the previous highest bid to the previous bidder:"]
    }), "\n", (0,jsx_runtime.jsx)(LiteralInclude, {
      file: "AuctionValidator.hs",
      language: "haskell",
      title: "Refunds previous highest bid condition",
      start: "-- BLOCK5",
      end: "-- BLOCK6"
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["It uses ", (0,jsx_runtime.jsx)(_components.code, {
        children: "PlutusTx.find"
      }), " to find the transaction output (a UTXO) that pays to the previous bidder the amount equivalent to the previous highest bid, and verifies that there is at least one such output."]
    }), "\n", (0,jsx_runtime.jsx)(_components.h3, {
      id: "correct-output-condition",
      children: "Correct Output Condition"
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["The ", (0,jsx_runtime.jsx)(_components.code, {
        children: "correctOutput"
      }), " condition verifies that the transaction produces a ", (0,jsx_runtime.jsx)(_components.em, {
        children: "continuing output"
      }), " (see below for definition) containing the correct datum and value.\nIt has two subconditions:"]
    }), "\n", (0,jsx_runtime.jsxs)(_components.ul, {
      children: ["\n", (0,jsx_runtime.jsxs)(_components.li, {
        children: [(0,jsx_runtime.jsx)(_components.code, {
          children: "correctOutputDatum"
        }), ": the datum should contain the new highest bid"]
      }), "\n", (0,jsx_runtime.jsxs)(_components.li, {
        children: [(0,jsx_runtime.jsx)(_components.code, {
          children: "correctOutputValue"
        }), ": the value should contain (1) the token being auctioned, and (2) the bid amount."]
      }), "\n"]
    }), "\n", (0,jsx_runtime.jsx)(LiteralInclude, {
      file: "AuctionValidator.hs",
      language: "haskell",
      title: "Correct new datum condition",
      start: "-- BLOCK6",
      end: "-- BLOCK7"
    }), "\n", (0,jsx_runtime.jsx)(_components.p, {
      children: "A \"continuing output\" is a transaction output that pays to the same script address from which we are currently spending.\nExactly one continuing output must be present in this example so that the next bidder can place a new bid.\nThe new bid, in turn, will need to spend the continuing output and get validated by the same script."
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["If the transaction is requesting a payout, the validator will then verify the other three conditions: ", (0,jsx_runtime.jsx)(_components.code, {
        children: "validPayoutTime"
      }), ", ", (0,jsx_runtime.jsx)(_components.code, {
        children: "sellerGetsHighestBid"
      }), " and ", (0,jsx_runtime.jsx)(_components.code, {
        children: "highestBidderGetsAsset"
      }), ".\nThese conditions are similar to the ones already explained, so their details are omitted."]
    }), "\n", (0,jsx_runtime.jsx)(_components.h3, {
      id: "compiling-the-validator",
      children: "Compiling the validator"
    }), "\n", (0,jsx_runtime.jsx)(_components.p, {
      children: "Finally, we need to compile the validator written in Plinth into Plutus Core, using the Plinth compiler:"
    }), "\n", (0,jsx_runtime.jsx)(LiteralInclude, {
      file: "AuctionValidator.hs",
      language: "haskell",
      title: "Compiling the validator",
      start: "-- BLOCK8",
      end: "-- BLOCK9"
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["The type of a compiled Plutus V3 spending validator should be ", (0,jsx_runtime.jsx)(_components.code, {
        children: "CompiledCode (BuiltinData -> BuiltinUnit)"
      }), ", as explained in ", (0,jsx_runtime.jsx)(_components.a, {
        href: "/pr-preview/docs/pr-7449/working-with-scripts/ledger-language-version",
        children: "Plutus Ledger Language Version"
      }), ".\nThe call to ", (0,jsx_runtime.jsx)(_components.code, {
        children: "PlutusTx.unsafeFromBuiltinData"
      }), " is the reason we need the ", (0,jsx_runtime.jsx)(_components.code, {
        children: "PlutusTx.unstableMakeIsData"
      }), " shown before, which derives ", (0,jsx_runtime.jsx)(_components.code, {
        children: "UnsafeFromData"
      }), " instances.\nAnd instead of returning a ", (0,jsx_runtime.jsx)(_components.code, {
        children: "Bool"
      }), ", it returns ", (0,jsx_runtime.jsx)(_components.code, {
        children: "BuiltinUnit"
      }), ", and the validation succeeds if the script evaluates without error."]
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["Note that ", (0,jsx_runtime.jsx)(_components.code, {
        children: "AuctionParams"
      }), " is ", (0,jsx_runtime.jsx)(_components.em, {
        children: "not"
      }), " an argument of the compiled validator.\n", (0,jsx_runtime.jsx)(_components.code, {
        children: "AuctionParams"
      }), " contains contract properties that don't change, so it is simply built into the validator by partial application.\nThe partial application is done via ", (0,jsx_runtime.jsx)(_components.code, {
        children: "PlutusTx.unsafeApplyCode"
      }), "."]
    }), "\n", (0,jsx_runtime.jsxs)(_components.blockquote, {
      children: ["\n", (0,jsx_runtime.jsxs)(_components.p, {
        children: ["📌", " ", (0,jsx_runtime.jsx)(_components.strong, {
          children: "NOTE"
        })]
      }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
        children: ["It is worth noting that we must call ", (0,jsx_runtime.jsx)(_components.code, {
          children: "PlutusTx.compile"
        }), " on the entire ", (0,jsx_runtime.jsx)(_components.code, {
          children: "auctionUntypedValidator"
        }), ", rather than applying it to ", (0,jsx_runtime.jsx)(_components.code, {
          children: "params"
        }), " before compiling, as in ", (0,jsx_runtime.jsx)(_components.code, {
          children: "$$(PlutusTx.compile [||auctionUntypedValidator params||])"
        }), ".\nThe latter won't work, because everything being compiled (inside ", (0,jsx_runtime.jsx)(_components.code, {
          children: "[||...||]"
        }), ") must be known at compile time, but we won't be able to access ", (0,jsx_runtime.jsx)(_components.code, {
          children: "params"
        }), " until runtime.\nInstead, once we have the ", (0,jsx_runtime.jsx)(_components.code, {
          children: "params"
        }), " value at runtime, we use ", (0,jsx_runtime.jsx)(_components.code, {
          children: "liftCodeDef"
        }), " or ", (0,jsx_runtime.jsx)(_components.code, {
          children: "liftCode"
        }), " to lift it into a Plutus Core term before calling ", (0,jsx_runtime.jsx)(_components.code, {
          children: "unsafeApplyCode"
        }), ".\nThis is the reason why we need the ", (0,jsx_runtime.jsx)(_components.code, {
          children: "Lift"
        }), " instance for ", (0,jsx_runtime.jsx)(_components.code, {
          children: "AuctionParams"
        }), ", derived via ", (0,jsx_runtime.jsx)(_components.code, {
          children: "PlutusTx.makeLift"
        }), ".\nTo learn more about lifting, see ", (0,jsx_runtime.jsx)(_components.a, {
          href: "/pr-preview/docs/pr-7449/using-plinth/lifting",
          children: "Lifting Values into CompiledCode"
        }), "."]
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