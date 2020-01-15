/*eslint-env node*/
'use strict';

exports.postMessage_ = function (ctx, msg) {
    ctx.postMessage(msg);
}

exports.registerOnMessage_ = function (ctx, f) {
  ctx.onmessage = function (e) {
    f(e.data)();
  };
};

exports.context = function () { return self; };