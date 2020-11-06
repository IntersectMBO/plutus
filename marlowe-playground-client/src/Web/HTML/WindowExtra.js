exports._close = function (window) {
  window.close();
};

exports._postMessage = function (message, window) {
  window.postMessage(message);
};
