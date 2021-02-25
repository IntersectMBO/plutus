"use strict";

exports.intersectionObserver = function (cb) {
  return function () {
    return new IntersectionObserver(function (entries, observer) {
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
        return observer.observe(element, config);
      };
    };
};

exports.disconnect = function (observer) {
  return function () {
    return observer.disconnect();
  };
};
