const {parser} = require('js2smt2');
const {
  astToJS,
  subsituteVariables,
  makeResidual,
  extractVariables,
  correctOne,
  correctAll,
} = require('../src/');

test('astToJS', () => {
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

  expect(Function(`
"use strict";
return (function (a, b) {
  ${astToJS(ast.body[0])}
})('hello', {type: 'there' , value: 0});
`)()).toEqual({state: 'branch1', outputs: {action1: 'a1', action2: 100}});

  expect(Function(`
"use strict";
return (function (a, b) {
  ${astToJS(ast.body[0])}
})('jello', {type: 'whirl' , value: 1});
`)()).toEqual({state: 'branch2', outputs: {action1: 'a2', action2: 200}});

});

test('subsituteVariables', () => {
  const ast = parser.parse(
      `a == 'hello' && b.type == 'there' && b.value * 1 === 0`);
  const varMap = {
    a: 'hello',
    b: {
      type: 'there',
      value: 0,
    }
  };
  const astSubed = subsituteVariables(ast, varMap);
  expect(astToJS(astSubed))
    .toBe(`((("hello" == "hello") && ("there" == "there")) && ((0 * 1) === 0))`);
});

test('subsituteVariables - MemberExpression', () => {
  const ast = parser.parse(`b["type"]`);
  const varMap = {
    b: {
      type: 'there',
    }
  };
  const astSubed = subsituteVariables(ast, varMap);
  expect(astToJS(astSubed))
    .toBe(`"there"`);
});

test('makeResidual', () => {
  const transAst = parser.parse(`
if (state == 'A' && b.value < 1) {
  return 'A';
} else if (state == 'A' && b.value < paramA) {
  return 'B';
} else {
  return 'C';
}
`);
  const trace = {
    state: 'A',
    b: {value: 0},
  }

  const residualAst = makeResidual(transAst, trace);

  expect(residualAst).toEqual({
    "type": "Program",
    "body": [
      {
        "type": "IfStatement",
        "test": {
          "type": "Literal",
          "value": true
        },
        "consequent": {
          "type": "BlockStatement",
          "body": [
            {
              "type": "ReturnStatement",
              "argument": {
                "type": "Literal",
                "value": "A"
              }
            }
          ]
        },
        "alternate": {
          "type": "IfStatement",
          "test": {
            "type": "BinaryExpression",
            "operator": "<",
            "left": {
              "type": "Literal",
              "value": 0
            },
            "right": {
              "type": "Identifier",
              "name": "paramA"
            }
          },
          "consequent": {
            "type": "BlockStatement",
            "body": [
              {
                "type": "ReturnStatement",
                "argument": {
                  "type": "Literal",
                  "value": "B"
                }
              }
            ]
          },
          "alternate": {
            "type": "BlockStatement",
            "body": [
              {
                "type": "ReturnStatement",
                "argument": {
                  "type": "Literal",
                  "value": "C"
                }
              }
            ]
          }
        }
      }
    ]
  });
});

test('makeResidual - two "from" states', () => {
  const transAst = parser.parse(`
if (state == 'A' && b.value < paramA) {
  return 'A';
} else if (state == 'B' && b.value < paramB) {
  return 'B';
} else {
  return 'C';
}
`);
  const trace = {
    state: 'A',
    b: {value: 0},
  }

  const residualAst = makeResidual(transAst, trace);

  expect(residualAst).toEqual({
    "type": "Program",
    "body": [
      {
        "type": "IfStatement",
        "test": {
          "type": "BinaryExpression",
          "operator": "<",
          "left": {
            "type": "Literal",
            "value": 0
          },
          "right": {
            "type": "Identifier",
            "name": "paramA"
          }
        },
        "consequent": {
          "type": "BlockStatement",
          "body": [
            {
              "type": "ReturnStatement",
              "argument": {
                "type": "Literal",
                "value": "A"
              }
            }
          ]
        },
        "alternate": {
          "type": "BlockStatement",
          "body": [
            {
              "type": "ReturnStatement",
              "argument": {
                "type": "Literal",
                "value": "C"
              }
            }
          ]
        }
      }
    ]
  });
});

test('extractVariables', () => {
  const ast = parser.parse(
      `a == 'hello' && b.type == 'there' && b.value * 1 === 0`);
  const variables = extractVariables(ast);
  expect(variables.sort()).toEqual(["a", "b"]);
});

test('correctOne', () => {
  const transAst = parser.parse(`
if (state == 'A' && b.value > paramA) {
  return 'B';
} else if (state == 'A' && b.value > paramB) {
  return 'A';
} else {
  return state;
}
`);
  const parameterMap = {
    paramA: 0,
    paramB: 2,
  };
  const trace = {
    state: 'A',
    b: {value: 0},
  }
  const correction = 'B';

  const formula = correctOne(transAst, parameterMap, trace, correction);

  expect(formula).toBe('(= "B" (ite (> 0 (+ 0 delta_paramA)) "B" (ite (> 0 (+ 2 delta_paramB)) "A" "A")))');
});

test('correctAll', () => {
  const transAst = parser.parse(`
if (state == 'A' && b.value > paramA) {
  return 'B';
} else if (state == 'B' && b.value <= paramA) {
  return 'A';
} else {
  return state;
}
`);
  const parameterMap = {
    paramA: 2,
  };
  const traces = [
    {
      timestamp: 0,
      trace: {
        state: 'A',
        b: {value: 1},
      }
    },
    {
      timestamp: 1,
      trace: {
        state: 'B',
        b: {value: -1},
      }
    }
  ]
  const corrections = [
    {
      timestamp: 0,
      correction: 'B'
    },
    {
      timestamp: 1,
      correction: 'A'
    }
  ];

  console.log(astToJS(makeResidual(transAst, traces[0].trace)));

  const formula = correctAll(transAst, parameterMap, traces, corrections);
  console.log('formula', formula);

  expect(true).toBe(false);
});
