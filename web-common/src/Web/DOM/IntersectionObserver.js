"use strict";

exports._intersectionObserver = function (config) {
  return function (cb) {
    return function () {
      return new IntersectionObserver(function (entries, observer) {
        return cb(entries)(observer)();
      }, config);
    };
  };
};

exports.observe = function (element) {
  return function (observer) {
    return function () {
      return observer.observe(element);
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
