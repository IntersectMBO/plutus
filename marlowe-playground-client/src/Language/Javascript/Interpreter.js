/*eslint-env node*/
'use strict';
const safeEval = require('notevil')

exports.eval_ = function (left, right, javascript) {
  // include any libraries etc we want by providing a context. be careful!
  // here we can pass in our library for constructing contracts
  var context = require('src/Language/Javascript/MarloweJS.ts');
  context['bignumber'] = require('bignumber');
  try {
    var justCode = javascript.split(/^.*\/\* === Code above this comment will be removed at compile time === \*\/$/gm).slice(1).join('');
    let res = safeEval(justCode, context);
    return right(JSON.stringify(res));
  } catch (error) {
    return (left(error.toString()));
  }
}
