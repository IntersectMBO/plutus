exports._unsafeReadBlocklyEventType = function (nothing, just, name, value) {
    var proto = Object.getPrototypeOf(value);
    if ('type' in proto && proto.type === name) {
      return just(value);
    } else {
      return nothing;
    }
}

exports._unsafePropertyMaybeUndefined = function (nothing, just, property, event) {
    if (typeof event !== 'object') {
      return nothing;
    } else {
      if (property in event && typeof event[property] !== 'undefined') {
        return just(event[property])
      } else {
        return nothing;
      }
    }
}

