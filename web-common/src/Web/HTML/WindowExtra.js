exports._close = function (window) {
  window.close();
};

exports._postMessage = function (message, targetOrigin, window) {
  window.postMessage(message, targetOrigin);
};

exports._matchMedia = function (query, window) {
  console.log("calling matchmedia", query);
  return window.matchMedia(query);
};

exports._matches = function (mediaQueryList) {
  console.log("calling matches");

  return mediaQueryList.matches;
};
