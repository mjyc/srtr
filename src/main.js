const {parser} = require('js2smt2');
const {astFilter, pEval} = require('../src/');

const ast = parser.parse(`
if (a == 'hello' && b.type == 'there' && b.value * 1 === 0) {
  return {
    state: 'branch1',
    outputs: {
      action1: 'a1',
      action2: 100,
    },
  };
} else if (a == 'jello' && b.type == 'whirl' && b.value + 1 === 2) {
  return {
    state: 'branch2',
    outputs: {
      action1: 'a2',
      action2: 200,
    },
  };
} else {
  return {
    state: 'branch3',
    outputs: {
      action1: 'a3',
      action2: 300,
    },
  };
}
`);

function paramMapToJS(paramMap) {
  return Object.keys(paramMap).map(function(pm) {
    return `var ${k} = ${JSON.stringify(pm[k])};`
  }).join('\n');
}

const parameterMap = {
  a: 'hello',
  b: {type: 'world', value: 0},
};

function selectSubtree(ast) {
  if (ast.type === 'BlockStatement') {
    if (ast.body.length > 1) {
      throw new Error(`BlockStatement is not supported for ast.body.length=${ast.body.length} > 1`);
    }
    return ast.body.map(function(b) {return `${interp(b)}`;}).join(' ');
  } else if (ast.type === 'IfStatement') {
    const testVal = Function(`
"use strict";
return function() {
${paramMapToJS(parameterMap)}
${astToJS(ast.test)}
}()`)();
    return testVal ? ast.consequent : selectSubtree(ast.consequent);
  } else {
    throw new Error(`Invalid input ast=${JSON.stringify(ast)}`);
  }
}

selectSubtree(ast)
