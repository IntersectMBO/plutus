/*eslint-env node*/
'use strict';
const safeEval = require('safe-eval')

exports.eval_ = function (left, right, model) {
  // include any libraries etc we want by providing a context. be careful!
  // here we can pass in our library for constructing contracts
  var monaco = global.monaco;
  var context = require('src/Language/Javascript/MarloweJS.ts');
  context['bignumber'] = require('bignumber.js');
  return monaco.languages.typescript.getTypeScriptWorker()
          .then(function(worker) {
              return (worker(model.uri)
                  .then(function(proxy) {
                      return proxy.getEmitOutput(model.uri.toString())
                                    .then((r) => {
                        var javascript = r.outputFiles[0].text;
                        try {
                          var slices = javascript.split(/^.*\/\* === Code above this comment will be removed at compile time === \*\/$/gm);
                          var takeSlice = 0;
                          if (slices.length > 1) { takeSlice = 1 };
                          var justCode = 'function () {' + slices.slice(takeSlice).join('') + '\n return contract; }';
                          let res = safeEval(justCode, context)();
                          return right(JSON.stringify(res));
                        } catch (error) {
                          return left(error.toString());
                        }
                    });
                }));
          })
}
