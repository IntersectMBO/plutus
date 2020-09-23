/*eslint-env node*/
'use strict';

exports.sendContractToShiny = function (datum) {
  return function () {
    return document.getElementById('shiny').contentWindow.postMessage(datum, "*");
  };
};
