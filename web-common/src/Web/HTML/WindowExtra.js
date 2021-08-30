exports._close = function (window) {
  window.close();
};

exports._postMessage = function (message, targetOrigin, window) {
  window.postMessage(message, targetOrigin);
};

exports._matchMedia = function (query, window) {
  return window.matchMedia(query);
};

exports._matches = function (mediaQueryList) {
  return mediaQueryList.matches;
};
