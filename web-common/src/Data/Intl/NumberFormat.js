'use strict';

var language = navigator ? navigator.language || 'en-US' : 'en-US';

exports.format_ = function (n) {
  return new Intl.NumberFormat(language).format(n)
};
