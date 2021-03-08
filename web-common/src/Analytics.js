/*eslint-env node*/
/*global exports gtag, analytics*/
'use strict';

exports.trackEvent_ = function (action, category, label, value) {
    // Google Analytics, the default.
    if (gtag) {
        gtag('event', action, {
            'event_category': category,
            'event_label': label,
            'value': value
        });
    };
};

exports.trackSegmentEvent_ = function (action, payload) {
    // Segment.com.
    if (typeof analytics !== 'undefined') {
        analytics.track(action, payload);
    };
};
