"use strict";

function astMap(tree, leafFnc, nodeFnc) {
  function map(ast) {
    if (ast.type === 'Identifier' || ast.type === 'Literal') {
      return leafFnc(ast);
    } else {
      var newNode = Object.keys(ast).reduce(function(prev, k) {
        if (Array.isArray(ast[k])) {
          prev[k] = ast[k]
            .map(function(n) {return map(n);})
        } else if (typeof ast[k] === 'object' && ast[k] !== null) {
          prev[k] = map(ast[k]);
        } else {
          prev[k] = ast[k];
        }
        return prev;
      }, {});
      return nodeFnc(newNode);
    }
  }
  return map(tree);
}

function astReduce(tree, leafFnc, nodeFnc, init) {
  function reduce(acc, ast) {
    if (ast.type === 'Identifier' || ast.type === 'Literal') {
      return leafFnc(acc, ast);
    } else {
      var newNode = Object.keys(ast).reduce(function(prev, k) {
        if (Array.isArray(ast[k])) {
          prev[k] = ast[k]
            .map(function(n) {return reduce(acc, n);})
        } else if (typeof ast[k] === 'object' && ast[k] !== null) {
          prev[k] = reduce(acc, ast[k]);
        } else {
          prev[k] = ast[k];
        }
        return prev;
      }, {});
      return nodeFnc(acc, newNode);
    }
  }
  return reduce(init, tree);
}


module.exports = {
  astMap: astMap,
  astReduce: astReduce,
}
