exports._arrow = function (element, padding) {
  const modifier = require("@popperjs/core/lib/modifiers/arrow").default;
  return Object.assign({}, modifier, {
    options: { element, padding },
  });
};

exports._popperOffsets = function () {
  return require("@popperjs/core/lib/modifiers/popperOffsets").default;
};

exports._computeStyles = function (options) {
  const modifier =
    require("@popperjs/core/lib/modifiers/computeStyles").default;
  return Object.assign({}, modifier, {
    options,
  });
};

exports._applyStyles = function () {
  return require("@popperjs/core/lib/modifiers/applyStyles").default;
};

exports._eventListeners = function (options) {
  const modifier =
    require("@popperjs/core/lib/modifiers/eventListeners").default;
  return Object.assign({}, modifier, {
    options,
  });
};

exports._offset = function (options) {
  const modifier = require("@popperjs/core/lib/modifiers/offset").default;
  return Object.assign({}, modifier, {
    options,
  });
};

exports._preventOverflow = function (options) {
  const modifier =
    require("@popperjs/core/lib/modifiers/preventOverflow").default;
  return Object.assign({}, modifier, {
    options,
  });
};

exports._flipPlacement = function (options) {
  const modifier =
    require("@popperjs/core/lib/modifiers/flip").default;
  return Object.assign({}, modifier, {
    options,
  });
};


exports._createPopper = function (reference, popper, options) {
  const { createPopper } = require("@popperjs/core/lib/createPopper");
  return createPopper(reference, popper, options);
};

exports._destroyPopper = function (instance) {
  instance.destroy();
};

exports._forceUpdate = function (instance) {
  instance.forceUpdate();
};
