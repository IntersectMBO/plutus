/*eslint-env node*/
'use strict';

exports._setItem = function (key, value) {
    return function() {
        window.localStorage.setItem(key, value);
    };
};

exports._getItem = function (key) {
    return function() {
        return window.localStorage.getItem(key);
    };
};

exports._listen = function (toRawStorageEvent, callback) {
    var onStorageEvent = function(event) {
        if (event.storageArea === window.localStorage) {
            var rawStorageEvent = toRawStorageEvent(event.key, event.oldValue, event.newValue);
            return callback(rawStorageEvent)();
        } else {
            return null;
        };
    };

    var canceler = function (error) {
        return function () {
            window.removeEventListener('storage', onStorageEvent, false);
        };
    };

    return function() {
        window.addEventListener('storage', onStorageEvent, false);
        return canceler;
    };
};

exports._getItems  = function (toRawStorageEvent) {
    return function () {
        var events = [];
        var i;

        for (i = 0; i < window.localStorage.length; i++) {
            var key = window.localStorage.key(i);
            var value = window.localStorage.getItem(key);
            var rawStorageEvent = toRawStorageEvent(key, null, value);
            events.push(rawStorageEvent);
        }

        return events;
    };
};
