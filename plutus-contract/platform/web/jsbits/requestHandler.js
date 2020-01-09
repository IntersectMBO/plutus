/*
   The Plutus program will export the request handler by calling
   h$plutusRequestHandler.setCallback after starting up.

   The contract loader should expose h$plutusRequestHandler.public
   to the environment that uses the contract.

   h$plutusRequestHandler.public implements the following functionality:

     - execute: runs a web service request.

 */

var h$plutusRequestHandler = (function() {
  var hsCallback = null,
      queue      = [],
      emptyBuffer = h$newByteArray(0);

  function convertStringLike(x) {
    if (typeof x === "string") {
      var r = h$encodeUtf8(x);
      r.len--;
      return r;
    }
    if (x && typeof x === "object") {
      if(ArrayBuffer.isView(x)) {
        var len          = x.byteLength;
        var offset       = x.byteOffset;
        var copiedBuffer = x.buffer.slice(offset, offset+len);
        return h$wrapBuffer(copiedBuffer, false, 0, len);

      } else if (x instanceof ArrayBuffer) {
        return h$wrapBuffer(x.slice(0, x.byteLength), false, 0, x.byteLength);
      }
    }
    return emptyBuffer;
  };

  function convertHeaders(xs) {
      var res = []; // , i, hdr;
      xs.forEach(hdr => {
        if (hdr && hdr.length === 2) {
          res.push([convertStringLike(hdr[0]), convertStringLike(hdr[1])]);
        }
      });
      /*
      for (i = 0; i < xs.length; i++) {
        hdr = xs[i];
        if (hdr && hdr.length === 2) {
          res.push([convertStringLike(hdr[0]), convertStringLike(hdr[1])]);
        }
      }
      */
      return res;
    };

  function decodeBuf(buf) {
    return h$decodeUtf8( h$wrapBuffer(buf, false, 0, buf.byteLength)
                       , buf.byteLength
                       , 0);
  };

  return {
      setCallback: function(cb) {
        hsCallback = cb;
        if(hsCallback) {
          // execute all queued requests
          var q = queue;
          queue = [];
          q.forEach(function(req) { hsCallback(req); });
        }
      }
    , respond:
      function(status, headers, body, callback) {
        callback({ status: status
                 , headers: headers.map(hdr => hdr.map(decodeBuf))
                 , body: body
                 , decodedBody: decodeBuf(body)
                 });
      }
    , public: {
        execute:
      /**
       * Request options
       * @typedef {Object} RequestOptions
       * @property {string|ArrayBuffer|TypedArray} [body] - Request body
       * @property {string[[]]} [headers] - Request headers, e.g. [["Accept-Language, "en"], ["Accept-Charset", "utf-8"]]
       *
       * Response data
       * @typedef {Object} Response
       * @property {int}    status - status code
       * @property {string[[]]} headers - response headers
       * @property {string} responseText - text value of the response
       * @property {ArrayBuffer} responseBuffer - ArrayBuffer value of the response
       *
       * Execute a plutus contract request
       * @param {string|ArrayBuffer|TypedArray} method - request method, e.g. "GET", "POST"
       * @param {string|ArrayBuffer|TypedArray} uri - location, e.g. "/", "/foo?bar=baz"
       * @param {RequestOptions} options - request options
       * @param {function} callback - callback, will be called with @Response
       */
      function(method, url, options, callback) {
        options = options || {};
        var opts = { body:    convertStringLike(options.body || "")
                   , headers: convertHeaders(options.headers)
                   };
        var req = { method:   convertStringLike(method || "GET")
                  , url:      convertStringLike(url    || "/")
                  , callback: callback || function() {}
                  , options:  opts
                  };
        if(hsCallback) {
          hsCallback(req);
        } else {
          queue.push(req);
        }
      }
    }
    };
})();
