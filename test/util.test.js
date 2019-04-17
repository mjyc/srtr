const {parser} = require('js2smt2');
const {
  astReduce,
} = require('../src/utils');

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

  expect(hasIdentifier(parser.parse(`a == 'hello' && b == 'there'`)))
    .toBe(true);
  expect(hasIdentifier(parser.parse(`'hello' !== 'there'`)))
    .toBe(false);
  expect(hasIdentifier(parser.parse(`o["m"]`)))
    .toBe(true);
  expect(hasIdentifier(parser.parse(`o[m]`)))
    .toBe(true);
  expect(hasIdentifier(parser.parse(`o.m`)))
    .toBe(true);
});
