#include <ghcjs/rts.h>

function h$createWebSocket(url, protocols) {
  return new WebSocket(url, protocols);
}

/*
   this must be called before the websocket has connected,
   typically synchronously after creating the socket
 */
function h$openWebSocket(ws, mcb, ccb, c) {
  if(ws.readyState !== 0) {
    throw new Error("h$openWebSocket: unexpected readyState, socket must be CONNECTING");
  }
  ws.lastError = null;
  ws.onopen = function() {
    if(mcb) {
      ws.onmessage = mcb;
    }
    if(ccb || mcb) {
      ws.onclose = function(ce) {
        if(ws.onmessage) {
          h$release(ws.onmessage);
          ws.onmessage = null;
        }
        if(ccb) {
          h$release(ccb);
          ccb(ce);
        }
      };
    };
    ws.onerror = function(err) {
      ws.lastError = err;
      if(ws.onmessage) {
        h$release(ws.onmessage);
        ws.onmessage = null;
      }
      ws.close();
    };
    c(null);
  };
  ws.onerror = function(err) {
    if(ccb) h$release(ccb);
    if(mcb) h$release(mcb);
    ws.onmessage = null;
    ws.close();
    c(err);
  };
}

function h$closeWebSocket(status, reason, ws) {
  ws.onerror = null;
  if(ws.onmessage) {
    h$release(ws.onmessage);
    ws.onmessage = null;
  }
  ws.close(status, reason);
}
