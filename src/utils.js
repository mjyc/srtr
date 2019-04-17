"use strict";

function astReduce(ast, leafFnc, nodeFnc) {
  if (ast.type === 'Identifier' || ast.type === 'Literal') {
    return leafFnc(ast);
  } else {
    var node = Object.keys(ast).reduce(function(prev, k) {
      if (Array.isArray(ast[k])) {
        prev[k] = ast[k].map(function(n) {return astReduce(n, leafFnc, nodeFnc);})
      } else if (typeof ast[k] === 'object' && ast[k] !== null) {
        prev[k] = astReduce(ast[k], leafFnc, nodeFnc);
      } else {
        prev[k] = ast[k];
      }
      return prev;
    }, {});
    return nodeFnc(node);
  }
}


module.exports = {
  astReduce: astReduce,
}
