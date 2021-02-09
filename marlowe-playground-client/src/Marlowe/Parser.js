/*eslint-env node*/
'use strict';

const nearley = require("nearley");
const grammar = require("grammar");
exports.parse_ = function (emptyInputError, parserError, success, fs, input) {
    if (!input) {
        return emptyInputError;
    }
    const parser = new nearley.Parser(nearley.Grammar.fromCompiled(grammar(fs)));
    try {
        parser.feed(input);
        return success(parser.results[0]);
    } catch (error) {
        if (error.token) {
            return parserError({ message: error.message, row: error.token.line, column: error.token.col, token: error.token.value });
        } else {
            const message =  getErrorMessage(error);
            console.log(message);
            return parserError({ message, row: 1, column: 0, token: "" });
        }
    }
}

function getErrorMessage(error) {
  if (typeof error === 'string') {
    return error;
  }
  if (typeof error === 'object' && error !== null && 'message' in error) {
    return error.message;
  }
  return 'Unexpected error: ' + error;
}
