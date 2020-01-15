/*eslint-env node*/
'use strict';

const Worker = require('output/worker.js');

exports.spawn = function () {
    return new Worker();
}

exports.postMessage_ = function (worker, msg) {
    worker.postMessage(msg);
}

exports.registerOnMessage_ = function (worker, f) {
    worker.onmessage = function (e) {
        f(e.data)();
    };
};
