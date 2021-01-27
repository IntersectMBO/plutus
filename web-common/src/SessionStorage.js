exports._setItem = function (key, value) {
    window.sessionStorage.setItem(key, value);
};

exports._getItem = function (key) {
    return window.sessionStorage.getItem(key);
};
