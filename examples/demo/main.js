const spawn = require("child_process").spawn;
const { interpret, jsParser } = require("z3js");
const { createSRTRSMT2, sexpParser } = require("../../");

const transAst = jsParser.parse(`
if (state == 'A' && b.value > paramA) {
  return 'B';
} else if (state == 'B' && b.value <= paramA) {
  return 'A';
} else {
  return state;
}
`);

const paramMap = {
  paramA: 2
};

const traces = [
  {
    timestamp: 0,
    trace: {
      state: "A",
      b: { value: 1 }
    }
  },
  {
    timestamp: 1,
    trace: {
      state: "B",
      b: { value: -1 }
    }
  }
];

const corrections = [
  {
    timestamp: 0,
    correction: "B"
  },
  {
    timestamp: 1,
    correction: "A"
  }
];

const options = { H: 1 };

const z3Input = createSRTRSMT2(
  transAst,
  paramMap,
  traces,
  corrections,
  options
);

const p = spawn("z3", ["-T:5", "-smt2", "-in"], {
  stdio: ["pipe", "pipe", "ignore"]
});
p.stdin.write(z3Input);
p.stdin.end();
p.stdout.on("data", data => {
  console.log(data.toString());
  if (!data.toString().startsWith("sat")) {
    const modelAst = sexpParser.parse(data.toString());
    const results = modelAst.value.splice(1).reduce((acc, v) => {
      if (
        v.type === "Expression" &&
        v.value[1].type === "Atom" &&
        v.value[1].value.type === "Identifier" &&
        (/w[0-9]+/.test(v.value[1].value.name) ||
          /^delta_./.test(v.value[1].value.name)) &&
        v.value[4].type === "Atom" &&
        v.value[4].value.type === "Literal"
      ) {
        acc[v.value[1].value.name] = v.value[4].value.value;
      }
      return acc;
    }, {});
    console.log("results", results);
  }
});
