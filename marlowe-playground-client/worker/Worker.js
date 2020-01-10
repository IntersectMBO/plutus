/*eslint-env node*/
'use strict';

exports.postMessage_ = function (worker, msg) {
    worker.postMessage(msg);
}

exports.registerOnMessage_ = function (ctx, f) {
  ctx.onmessage = function (e) {
    f(e.data)();
  };
};

exports.context = function () { return self; };