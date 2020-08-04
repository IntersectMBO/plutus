/*eslint-env node*/
'use strict';
const safeEval = require('notevil')

exports.eval_ = function (left, right, javascript) {
  // include any libraries etc we want by providing a context. be careful!
  const context = { JSON: JSON }
  try {
    console.log(javascript);
    let res = safeEval(javascript, context);
    console.log(res);
    return right(res);
  } catch (error) {
    return (left(error.toString()));
  }
}