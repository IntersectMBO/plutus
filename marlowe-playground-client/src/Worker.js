/*eslint-env node*/
'use strict';

const Worker = require('output/worker.js');

exports.spawn = function () {
    return new Worker();
}

exports.analyseContract_ = function (worker, contractString) {
    worker.postMessage({messageType: "AnalyseContract", body: contractString });
}