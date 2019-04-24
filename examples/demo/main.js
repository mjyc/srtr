const spawn = require('child_process').spawn;
const {interpret, parser} = require('js2smt2');

const JS_CODE = `
function f(a, b) {
  if (a == 'hello' && b.type == 'there' && b.value * 1 === 0) {
    return 'branch1';
  } else if (a == 'jello' && b.type == 'whirl' && b.value + 1 === 2) {
    return 'branch2';
  } else {
    return 'branch3';
  }
}
`;

const typeDefs = {
  f: {
    a: 'String',
    b: '(B String Int)',
    return: 'String',
  }
}

const z3Input = `
(declare-datatypes (T1 T2) ((B (mk-input (type T1) (value T2)))))
${interpret(parser.parse(JS_CODE).body[0], typeDefs)}

(declare-const x String)
(declare-const y (B String Int))
(assert (= (f x y) "branch2"))
(check-sat)
(get-model)
`;

const p = spawn('z3', ['-T:5', '-smt2', '-in'], {stdio: ['pipe', 'pipe', 'ignore']});
p.stdin.write(z3Input);
p.stdin.end();
p.stdout.on('data', (data) => {
  console.log(data.toString());
});
