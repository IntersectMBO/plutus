/*eslint-env node*/
'use strict';

exports.handler = function (e) {
  console.log('Worker: Message received from main script!');
  console.log(e.data);
  let result = e.data[0] * e.data[1];
  if (isNaN(result)) {
    postMessage('Please write two numbers');
  } else {
    let workerResult = 'Result: ' + result;
    console.log('Worker: Posting message back to main script');
    postMessage(workerResult);
  }
}

exports.registerOnMessage = function (ctx, f) {
  ctx.onmessage = function (e) {
    f(e.data);
  };
};

exports.context = function () { return self; };

exports.getMessageData = function (msg) {
  return msg.data;
}