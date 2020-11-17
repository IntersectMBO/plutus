exports._close = function (window) {
  window.close();
};

exports._postMessage = function (message, targetOrigin, window) {
  window.postMessage(message, targetOrigin);
};
