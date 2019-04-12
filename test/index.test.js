const {parser} = require('js2smt2');
const {
  astFilter,
  astToJS,
  makeResidual
} = require('../src/');

test('astFilter', () => {
  const ast = parser.parse(`
function f(a, b) {
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
}
`);

  const filtered = astFilter(
    ast,
    function (ast) {
      return !(
        ast.type === 'Property'
        && ast.key.type === 'Identifier'
        && ast.key.name === 'outputs'
      );
    },
  );

  expect(filtered).toEqual({
    "type": "Program",
    "body": [
        {
          "type": "FunctionDeclaration",
          "id": {
              "type": "Identifier",
              "name": "f"
          },
          "params": [
              {
                "type": "Identifier",
                "name": "a"
              },
              {
                "type": "Identifier",
                "name": "b"
              }
          ],
          "body": {
              "type": "BlockStatement",
              "body": [
                {
                    "type": "IfStatement",
                    "test": {
                      "type": "LogicalExpression",
                      "operator": "&&",
                      "left": {
                          "type": "LogicalExpression",
                          "operator": "&&",
                          "left": {
                            "type": "BinaryExpression",
                            "operator": "==",
                            "left": {
                                "type": "Identifier",
                                "name": "a"
                            },
                            "right": {
                                "type": "Literal",
                                "value": "hello"
                            }
                          },
                          "right": {
                            "type": "BinaryExpression",
                            "operator": "==",
                            "left": {
                                "type": "MemberExpression",
                                "object": {
                                  "type": "Identifier",
                                  "name": "b"
                                },
                                "property": {
                                  "type": "Identifier",
                                  "name": "type"
                                },
                                "computed": false
                            },
                            "right": {
                                "type": "Literal",
                                "value": "there"
                            }
                          }
                      },
                      "right": {
                          "type": "BinaryExpression",
                          "operator": "===",
                          "left": {
                            "type": "BinaryExpression",
                            "operator": "*",
                            "left": {
                                "type": "MemberExpression",
                                "object": {
                                  "type": "Identifier",
                                  "name": "b"
                                },
                                "property": {
                                  "type": "Identifier",
                                  "name": "value"
                                },
                                "computed": false
                            },
                            "right": {
                                "type": "Literal",
                                "value": 1
                            }
                          },
                          "right": {
                            "type": "Literal",
                            "value": 0
                          }
                      }
                    },
                    "consequent": {
                      "type": "BlockStatement",
                      "body": [
                          {
                            "type": "ReturnStatement",
                            "argument": {
                                "type": "ObjectExpression",
                                "properties": [
                                  {
                                      "type": "Property",
                                      "key": {
                                        "type": "Identifier",
                                        "name": "state"
                                      },
                                      "value": {
                                        "type": "Literal",
                                        "value": "branch1"
                                      },
                                      "kind": "init"
                                  },
                                ]
                            }
                          }
                      ]
                    },
                    "alternate": {
                      "type": "IfStatement",
                      "test": {
                          "type": "LogicalExpression",
                          "operator": "&&",
                          "left": {
                            "type": "LogicalExpression",
                            "operator": "&&",
                            "left": {
                                "type": "BinaryExpression",
                                "operator": "==",
                                "left": {
                                  "type": "Identifier",
                                  "name": "a"
                                },
                                "right": {
                                  "type": "Literal",
                                  "value": "jello"
                                }
                            },
                            "right": {
                                "type": "BinaryExpression",
                                "operator": "==",
                                "left": {
                                  "type": "MemberExpression",
                                  "object": {
                                      "type": "Identifier",
                                      "name": "b"
                                  },
                                  "property": {
                                      "type": "Identifier",
                                      "name": "type"
                                  },
                                  "computed": false
                                },
                                "right": {
                                  "type": "Literal",
                                  "value": "whirl"
                                }
                            }
                          },
                          "right": {
                            "type": "BinaryExpression",
                            "operator": "===",
                            "left": {
                                "type": "BinaryExpression",
                                "operator": "+",
                                "left": {
                                  "type": "MemberExpression",
                                  "object": {
                                      "type": "Identifier",
                                      "name": "b"
                                  },
                                  "property": {
                                      "type": "Identifier",
                                      "name": "value"
                                  },
                                  "computed": false
                                },
                                "right": {
                                  "type": "Literal",
                                  "value": 1
                                }
                            },
                            "right": {
                                "type": "Literal",
                                "value": 2
                            }
                          }
                      },
                      "consequent": {
                          "type": "BlockStatement",
                          "body": [
                            {
                                "type": "ReturnStatement",
                                "argument": {
                                  "type": "ObjectExpression",
                                  "properties": [
                                      {
                                        "type": "Property",
                                        "key": {
                                            "type": "Identifier",
                                            "name": "state"
                                        },
                                        "value": {
                                            "type": "Literal",
                                            "value": "branch2"
                                        },
                                        "kind": "init"
                                      },
                                  ]
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
                                  "type": "ObjectExpression",
                                  "properties": [
                                      {
                                        "type": "Property",
                                        "key": {
                                            "type": "Identifier",
                                            "name": "state"
                                        },
                                        "value": {
                                            "type": "Literal",
                                            "value": "branch3"
                                        },
                                        "kind": "init"
                                      },
                                  ]
                                }
                            }
                          ]
                      }
                    }
                }
              ]
          }
        }
    ]
  });
});

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
'use strict'
return (function (a, b) {
  ${astToJS(ast.body[0])}
})('hello', {type: 'there' , value: 0});
`)()).toEqual({state: 'branch1', outputs: {action1: 'a1', action2: 100}});

  expect(Function(`
'use strict'
return (function (a, b) {
  ${astToJS(ast.body[0])}
})('jello', {type: 'whirl' , value: 1});
`)()).toEqual({state: 'branch2', outputs: {action1: 'a2', action2: 200}});

});

test('makeResidual', () => {
  const ast = parser.parse(`
if (a == 'hello' && b.type == 'there' && b.value * 1 === 0) {
  return 'branch1';
} else if (a == 'jello' && b.type == 'whirl' && b.value + 1 === 2) {
  return 'branch2';
} else {
  return 'branch3';
}
`);
  const parameterMap = {
    a: 'hello',
    b: {type: 'there', value: 0},
  };
  const astIfStatement = ast.body[0];
  const subAst = makeResidual(astIfStatement, parameterMap);
  expect(subAst).toEqual({type: 'Literal', value: 'branch1'});
});