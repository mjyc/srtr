"use strict";
var js2smt2 = require('js2smt2');
var utils = require('../src/utils');

function astRemoveNode(ast, pred) {
  function filter(ast) {
    if (!pred(ast)) {
      return null;
    }

    return Object.keys(ast).reduce(function(prev, k) {
      if (Array.isArray(ast[k])) {
        prev[k] = ast[k]
          .map(function(elem) {return filter(elem);})
          .filter(function(elem) {return elem !== null});
      } else if (typeof ast[k] === 'object' && ast[k] !== null) {
        var t = filter(ast[k]);
        if (t !== null) {
          prev[k] = t;
        }
      } else {
        prev[k] = ast[k];
      }
      return prev;
    }, {});
  }

  return filter(ast);
}

function astToJS(ast) {
  if (ast.type === 'Identifier') {
    return ast.name;
  } else if (ast.type === 'UnaryExpression') {
    return `(${ast.operator} ${astToJS(ast.argument)})`;
  } else if (ast.type === 'BinaryExpression') {
    return `(${astToJS(ast.left)} ${ast.operator} ${astToJS(ast.right)})`;
  } else if (ast.type === 'LogicalExpression') {
    return `(${astToJS(ast.left)} ${ast.operator} ${astToJS(ast.right)})`;
  } else if (ast.type === 'ExpressionStatement') {
    return `${astToJS(ast.expression)}`;
  } else if (ast.type === 'Literal') {
    return `${typeof ast.value === 'string' ? JSON.stringify(ast.value) : ast.value}`;
  } else if (ast.type === 'ReturnStatement') {
    return `return ${astToJS(ast.argument)}`;
  } else if (ast.type === 'BlockStatement') {
    return ast.body.map(function(b) {return `${astToJS(b)};`;}).join(' ');
  } else if (ast.type === 'IfStatement') {
    return `if (${astToJS(ast.test)}) { ${astToJS(ast.consequent)} } else { ${astToJS(ast.alternate)} }`;
  } else if (ast.type === 'MemberExpression') {
    return `${astToJS(ast.object)}["${astToJS(ast.property)}"]`;
  } else if (ast.type === 'Property') {
    return `"${astToJS(ast.key)}": ${astToJS(ast.value)}`;
  } else if (ast.type === 'ObjectExpression') {
    return `{${ast.properties.map(function (property) {return astToJS(property);}).join(', ')}}`;
  } else if (ast.type === 'Program') {
    return ast.body.map(function (b) {return astToJS(b);}).join(' ');
  } else {
    throw new Error(`Invalid input ast=${JSON.stringify(ast)}`);
  }
}

function subsituteVariables(ast, variableMap) {
  function subsitute(ast, varMap) {
    if (ast.type === 'Identifier') {
      var value = varMap[ast.name];
      return typeof value === 'undefined' ? ast
        : {
          type: 'Literal',
          value: value,
        };
    } else if (ast.type === 'MemberExpression') {
      var object = subsitute(ast.object, varMap);
      var property = !ast.property.computed
        ? ast.property : subsitute(ast.property, varMap);
      return (typeof object.value === 'object' && object.value !== null)
        ? subsitute(
          property.type === 'Literal'
            ? {
              type: 'Identifier',
              name: property.value
            } : property,
          object.value
        ) : ast;
    }

    return Object.keys(ast).reduce(function(prev, k) {
      if (Array.isArray(ast[k])) {
        prev[k] = ast[k]
          .map(function(elem) {return subsitute(elem, varMap);});
      } else if (typeof ast[k] === 'object' && ast[k] !== null) {
        prev[k] = subsitute(ast[k], varMap);
      } else {
        prev[k] = ast[k];
      }
      return prev;
    }, {});
  }

  return subsitute(ast, variableMap);
}

function extractVariables(ast) {
  function extract(ast, vars) {
    if (ast.type === 'Identifier') {
      return vars.slice(0).concat(ast.name);
    } else if (ast.type === 'MemberExpression') {
      var objVars = extractVariables(ast.object, vars);
      var propVars = !ast.property.computed
        ? [] : extractVariables(ast.property, vars);
      return objVars.concat(propVars);
    }

    return Object.keys(ast).reduce(function(prev, k) {
      if (Array.isArray(ast[k])) {
        return prev.concat(
          ast[k]
            .map(function(elem) {return extract(elem, vars);})
            .reduce(function (prev, arr) { return prev.concat(arr); }, vars)
        );
      } else if (typeof ast[k] === 'object' && ast[k] !== null) {
        return prev.concat(extract(ast[k], vars));
      } else {
        return prev;
      }
    }, []);
  }

  var vars = extract(ast, []);
  return vars.filter(function(v, i){ return vars.indexOf(v) >= i; });
}

function hasIdentifier(tree) {
  return utils.astReduce(tree, function (acc, leaf) {
    return acc || leaf.type === 'Identifier';
  }, function (acc, node) {
    var updated = Object.keys(node).reduce(function (prev, k) {
      if (k === 'body') {
        return prev || node[k].reduce(function(p, b) {return p;} || b, false);
      } else if (
        k === 'right' || k === 'left'
        || k === 'object' || k === 'property'
        || k === 'expression'
        || k === 'argument'
        || k === 'test' || k === 'consequent' || k === 'alternate'
      ) {
        return prev || node[k];
      } else {
        return prev;
      }
    }, false);
    return acc || updated;
  }, false);
}

function pEval(ast, variableMap) {
  const subbedAst = subsituteVariables(ast, variableMap);
  return utils.astMap(subbedAst, function (leaf) {
    return leaf;
  }, function (node) {
    if (
      node.type === 'UnaryExpression' && node.argument.type === 'Literal'
      || (
        (node.type === 'BinaryExpression' || node.type === 'LogicalExpression')
        && node.left.type === 'Literal' && node.right.type === 'Literal'
      )
    ) {
      return {
        type: 'Literal',
        value: Function(`return ${astToJS(node)}`)(),
      };
    } else if (
      (node.type === 'LogicalExpression' && node.operator === '&&')
      && (
        (node.left.type === 'Literal' && !node.left.value)
        || (node.right.type === 'Literal' && !node.right.value)
      )
    ) {
      return {
        type: 'Literal',
        value: false,
      };
    } else if (
      (node.type === 'LogicalExpression' && node.operator === '||')
      && (
        (node.left.type === 'Literal' && node.left.value)
        || (node.right.type === 'Literal' && node.right.value)
      )
    ) {
      return {
        type: 'Literal',
        value: true,
      };
    } else if (
      (node.type === 'LogicalExpression' && node.operator === '&&')
      && (
        (node.left.type === 'Literal' && node.left.value)
        || (node.right.type === 'Literal' && node.right.value)
      )
    ) {
      return (node.left.type === 'Literal' && node.left.value)
        ? node.right : node.left;
    } else if (
      (node.type === 'LogicalExpression' && node.operator === '||')
      && (
        (node.left.type === 'Literal' && !node.left.value)
        || (node.right.type === 'Literal' && !node.right.value)
      )
    ) {
      return (node.left.type === 'Literal' && !node.left.value)
        ? node.left : node.right;
    } else {
      return node;
    }
  });
}

function makeResidual(transAst, paramMap, trace) {
  var evaledAst = pEval(transAst, trace);
  var subAst = utils.astMap(evaledAst, function(leaf) {
    return leaf;
  }, function (node) {
    if (node.type === 'IfStatement') {
      if (
        hasIdentifier(node.test)
        || (node.test.type !== 'Literal' || !!node.test.value)
      ) {
        return node;
      } else {
        return node.alternate;
      }
    } else {
      return Object.keys(node).reduce(function(prev, k) {
        if (Array.isArray(node[k])) {
          prev[k] = node[k].filter(function (n) {return n !== null;})
        } else if (typeof node[k] === 'object' && node[k] !== null) {
          prev[k] = node[k];
        } else {
          if (node[k] !== null) {
            prev[k] = node[k];
          }
        }
        return prev;
      }, {});
    }
  });

  // var subbedSubAst = subsituteVariables(subAst, paramMap);
  return subAst;
}

function correctOne(transAst, paramMap, trace, correction) {
  var residualAst = makeResidual(transAst, paramMap, trace);
  // var params = extractVariables(residualAst);
  return (`(= ${correction} ${js2smt2.interpret(residualAst)})`);
}

function correctAll(transAst, paramMap, traces, corrections) {
  return undefined;
}

function srtr(transAst, paramMap, trace, corrections) {
  return undefined;
}

module.exports = {
  astRemoveNode: astRemoveNode,
  astToJS: astToJS,
  subsituteVariables: subsituteVariables,
  extractVariables: extractVariables,
  pEval: pEval,
  makeResidual: makeResidual,
  correctOne: correctOne,
}
