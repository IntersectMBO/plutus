function initializeGA() {
  var t = document.createElement("script");
  t.type = "text/javascript";
  t.async = !0;
  t.src = "https://www.googletagmanager.com/gtag/js?id=" + window.googleAnalyticsId;
  var n = document.getElementsByTagName("script")[0];
  n.parentNode.insertBefore(t, n);
  window.dataLayer = window.dataLayer || [];
  function gtag() {
    dataLayer.push(arguments);
  }
  gtag("js", new Date());
  gtag("config", "{{ googleAnalyticsId }}", {
    anonymize_ip: true,
    custom_map: {
      dimension1: "product",
    },
    product: "Marlowe website",
  });
}
function initializeSegment() {
  var analytics = (window.analytics = window.analytics || []);
  if (!analytics.initialize)
    if (analytics.invoked) window.console && console.error && console.error("Segment snippet included twice.");
    else {
      analytics.invoked = !0;
      analytics.methods = [
        "trackSubmit",
        "trackClick",
        "trackLink",
        "trackForm",
        "pageview",
        "identify",
        "reset",
        "group",
        "track",
        "ready",
        "alias",
        "debug",
        "page",
        "once",
        "off",
        "on",
        "addSourceMiddleware",
        "addIntegrationMiddleware",
        "setAnonymousId",
        "addDestinationMiddleware",
      ];
      analytics.factory = function (e) {
        return function () {
          var t = Array.prototype.slice.call(arguments);
          t.unshift(e);
          analytics.push(t);
          return analytics;
        };
      };
      for (var e = 0; e < analytics.methods.length; e++) {
        var key = analytics.methods[e];
        analytics[key] = analytics.factory(key);
      }
      analytics.load = function (key, e) {
        var t = document.createElement("script");
        t.type = "text/javascript";
        t.async = !0;
        t.src = "https://cdn.segment.com/analytics.js/v1/" + key + "/analytics.min.js";
        var n = document.getElementsByTagName("script")[0];
        n.parentNode.insertBefore(t, n);
        analytics._loadOptions = e;
      };
      analytics.SNIPPET_VERSION = "4.13.1";
      analytics.load(window.segmentAnalyticsId);
      analytics.page();
    }
}
export function activateAnalytics() {
  initializeGA();
  initializeSegment();
}
