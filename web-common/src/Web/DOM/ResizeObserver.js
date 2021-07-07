"use strict";

exports.resizeObserver = function (cb) {
  return function () {
    return new ResizeObserver(function (entries, observer) {
      return cb(entries)(observer)();
    });
  };
};

exports._observe = function (element) {
  return function (config) {

    return function (observer) {

      return function () {

        return observer.observe(element, config);
      };
    };
  };
};

exports.unobserve = function (element) {
    return function (observer) {
      return function () {
        return observer.unobserve(element);
      };
    };
};

exports.disconnect = function (observer) {
  return function () {
    return observer.disconnect();
  };
};
