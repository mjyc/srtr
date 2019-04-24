const spawn = require('child_process').spawn;
const {interpret, parser} = require('js2smt2');
const {
  createSRTRSMT2,
  sexpParser,
} = require('../../');

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
];

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

const z3Input = createSRTRSMT2(
    transAst, parameterMap, traces, corrections, options
  ) + '\n(check-sat) (get-model)';

// console.log(z3Input);

// const z3Input = `
// (declare-datatypes (T1 T2) ((B (mk-input (type T1) (value T2)))))
// ${interpret(parser.parse(JS_CODE).body[0], typeDefs)}

// (declare-const x String)
// (declare-const y (B String Int))
// (assert (= (f x y) "branch2"))
// (check-sat)
// (get-model)
// `;

const p = spawn('z3', ['-T:5', '-smt2', '-in'], {stdio: ['pipe', 'pipe', 'ignore']});
p.stdin.write(z3Input);
p.stdin.end();
p.stdout.on('data', (data) => {
  // console.log(typeof data.toString())
  if (!data.toString().startsWith("sat")) {
    console.log(data.toString());
    console.log(sexpParser.parse(data.toString()));
  }
});
