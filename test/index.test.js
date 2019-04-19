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

  expect(astToJS(ast)).toBe(`if ((((a == "hello") && (b["type"] == "there")) && ((b["value"] * 1) === 0))) { return {"state": "branch1", "outputs": {"action1": "a1", "action2": 100}}; } else { if ((((a == "jello") && (b["type"] == "whirl")) && ((b["value"] + 1) === 2))) { return {"state": "branch2", "outputs": {"action1": "a2", "action2": 200}}; } else { return {"state": "branch3", "outputs": {"action1": "a3", "action2": 300}}; } }`);
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
if (state == 'A' && b.value > 10) {
  return 'B';
} else if (state == 'A' && b.value < paramA) {
  return 'C';
} else {
  return state;
}
`);
  const trace = {
    state: 'A',
    b: {value: 0},
  }

  const residualAst = makeResidual(transAst, trace);

  // if ((0 < paramA)) { return "C"; } else { return "A"; }
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
                "value": "C"
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
                "value": "A"
              }
            }
          ]
        }
      }
    ]
  });
});


test('makeResidual - two from states', () => {
  const transAst = parser.parse(`
if (state == 'A' && b.value > paramA) {
  return 'B';
} else if (state == 'B' && b.value > paramB) {
  return 'C';
} else {
  return state;
}
`);
  const trace = {
    state: 'A',  // try 'B' or 'C'
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
          "operator": ">",
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
                "value": "A"
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
} else if (state == 'B' && b.value > paramB) {
  return 'C';
} else {
  return state;
}
`);
  const parameterMap = {
    paramA: 0,
    paramB: 1,
  };
  const trace = {
    state: 'A',
    b: {value: 1},
  }
  const correction = 'A';

  const formula = correctOne(transAst, parameterMap, trace, correction);

  expect(formula).toBe('(= "A" (ite (> 1 (+ 0 delta_paramA)) "B" "A"))');
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

  const options = {H: 1};
  const formula = correctAll(
      transAst, parameterMap, traces, corrections, options);
  console.log('formula\n', formula);

  expect(true).toBe(false);
});


test('correctAll2', () => {
  const transAst = parser.parse(`
if (state == 'A' && input > paramA) {
  return 'B';
} else {
  return state;
}
`);
  const parameterMap = {
    paramA: 0,
  };
  const traces = [
    {
      timestamp: 0,
      trace: {
        state: 'A',
        input: 1,
      }
    },
    {
      timestamp: 1,
      trace: {
        state: 'A',
        input: 1.5,
      }
    },
    {
      timestamp: 2,
      trace: {
        state: 'A',
        input: 0.5,
      }
    },
    // {
    //   timestamp: 3,
    //   trace: {
    //     state: 'A',
    //     input: -1,
    //   }
    // },
    {
      timestamp: 4,
      trace: {
        state: 'A',
        input: -1,
      }
    },
    {
      timestamp: 5,
      trace: {
        state: 'A',
        input: -1.5,
      }
    },
    {
      timestamp: 6,
      trace: {
        state: 'A',
        input: -0.5,
      }
    },
    // {
    //   timestamp: 7,
    //   trace: {
    //     state: 'A',
    //     input: 1,
    //   }
    // },
  ]
  const corrections = [
    {
      timestamp: 0,
      correction: 'B'
    },
    {
      timestamp: 1,
      correction: 'B'
    },
    {
      timestamp: 2,
      correction: 'B'
    },
    // {
    //   timestamp: 3,
    //   correction: 'B'
    // },
    {
      timestamp: 4,
      correction: 'A'
    },
    {
      timestamp: 5,
      correction: 'A'
    },
    {
      timestamp: 6,
      correction: 'A'
    },
    // {
    //   timestamp: 7,
    //   correction: 'A'
    // }
  ];

  const options = {H: 1};
  const formula = correctAll(
      transAst, parameterMap, traces, corrections, options);
  console.log('formula\n', formula);

  expect(true).toBe(false);
});
