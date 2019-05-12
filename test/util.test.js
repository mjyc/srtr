const {jsParser} = require('js2smt2');
const {
  astMap,
  astReduce,
} = require('../src/utils');

test('astMap', () => {
  const subsitute = tree => astMap(tree, (leaf) => {
    return leaf.type === 'Identifier' ? {
      type: 'Literal',
      value: leaf.name,
    } : leaf;
  }, (node) => {
    return node;
  });

  expect(subsitute(jsParser.parse(`a === 'hello'`)))
    .toEqual({
       "type": "Program",
       "body": [
          {
             "type": "ExpressionStatement",
             "expression": {
                "type": "BinaryExpression",
                "operator": "===",
                "left": {
                   "type": "Literal",
                   "value": "a"
                },
                "right": {
                   "type": "Literal",
                   "value": "hello"
                }
             }
          }
       ]
    });
});

test('astReduce', () => {
  const hasIdentifier = tree => astReduce(tree, (acc, leaf) => {
    return acc || leaf.type === 'Identifier';
  }, (acc, node) => {
    const updated = Object.keys(node).reduce((prev, k) => {
      if (k === 'body') {
        return prev || node[k].reduce((p, b) => p || b, false);
      } else if (
        k === 'right' || k === 'left'
        || k === 'object' || k === 'property'
        || k === 'expression'
      ) {
        return prev || node[k];
      } else {
        return prev;
      }
    }, false);
    return acc || updated;
  }, false);

  expect(hasIdentifier(jsParser.parse(`a == 'hello' && b == 'there'`)))
    .toBe(true);
  expect(hasIdentifier(jsParser.parse(`'hello' !== 'there'`)))
    .toBe(false);
  expect(hasIdentifier(jsParser.parse(`o["m"]`)))
    .toBe(true);
  expect(hasIdentifier(jsParser.parse(`o[m]`)))
    .toBe(true);
  expect(hasIdentifier(jsParser.parse(`o.m`)))
    .toBe(true);
});
