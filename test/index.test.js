const { jsParser } = require("js2smt2");
const {
  astToJS,
  subsituteVariables,
  pEval,
  extractVariables,
  correctOne,
  correctAll,
  createSRTRSMT2
} = require("../src/");

test("astToJS", () => {
  const ast = jsParser.parse(`
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

  expect(astToJS(ast)).toBe(
    `if ((((a == "hello") && (b["type"] == "there")) && ((b["value"] * 1) === 0))) { return {"state": "branch1", "outputs": {"action1": "a1", "action2": 100}}; } else { if ((((a == "jello") && (b["type"] == "whirl")) && ((b["value"] + 1) === 2))) { return {"state": "branch2", "outputs": {"action1": "a2", "action2": 200}}; } else { return {"state": "branch3", "outputs": {"action1": "a3", "action2": 300}}; } }`
  );
});

test("subsituteVariables", () => {
  const ast = jsParser.parse(
    `a == 'hello' && b.type == 'there' && b.value * 1 === 0`
  );
  const varMap = {
    a: "hello",
    b: {
      type: "there",
      value: 0
    }
  };

  const subbedAst = subsituteVariables(ast, varMap);
  expect(astToJS(subbedAst)).toBe(
    `((("hello" == "hello") && ("there" == "there")) && ((0 * 1) === 0))`
  );
});

test("subsituteVariables - MemberExpression", () => {
  const ast = jsParser.parse(`b["type"]`);
  const varMap = {
    b: {
      type: "there"
    }
  };

  const astSubed = subsituteVariables(ast, varMap);
  expect(astToJS(astSubed)).toBe(`"there"`);
});

test("pEval - transition function", () => {
  const transAst = jsParser.parse(`
if (state == 'A' && b.value > param) {
  return 'B';
} else {
  return state;
}
`);
  const varMap = {
    state: "A",
    b: { value: 1 }
  };

  const evaledAst = pEval(transAst, varMap);
  expect(astToJS(evaledAst)).toBe(
    `if ((1 > param)) { return "B"; } else { return "A"; }`
  );
});

test("pEval - return", () => {
  const transAst = jsParser.parse(`
if (state == 'A' && b.value > param) {
  return 'B';
} else {
  return state;
}
`);
  const varMap = {
    state: "B",
    b: { value: 1 }
  };

  const evaledAst = pEval(transAst, varMap);
  expect(astToJS(evaledAst)).toBe(`return "B";`);
});

test("pEval - multiple branches", () => {
  const transAst = jsParser.parse(`
if (state == 'A' && b.value > param) {
  return 'B';
} else if (state == 'A' && b.value < 0) {
  return 'C';
} else {
  return state;
}
`);
  const varMap = {
    state: "A",
    b: { value: -1 }
  };

  const evaledAst = pEval(transAst, varMap);
  expect(astToJS(evaledAst)).toBe(
    `if ((-1 > param)) { return \"B\"; } else { return \"C\"; }`
  );
});

test("pEval - multiple branches with multiple from states", () => {
  const transAst = jsParser.parse(`
if (state == 'A' && b.value > paramA) {
  return 'B';
} else if (state == 'B' && b.value > paramB) {
  return 'C';
} else {
  return state;
}
`);
  const varMap = {
    state: "B",
    b: { value: 0 }
  };

  const evaledAst = pEval(transAst, varMap);
  expect(astToJS(evaledAst)).toEqual(
    `if ((0 > paramB)) { return "C"; } else { return "B"; }`
  );
});

test("extractVariables", () => {
  const ast = jsParser.parse(
    `a == 'hello' && b.type == 'there' && b.value * 1 === 0`
  );
  const variables = extractVariables(ast);

  expect(variables.sort()).toEqual(["a", "b", "type", "value"]);
});

test("correctOne", () => {
  const transAst = jsParser.parse(`
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
    paramB: 1
  };
  const trace = {
    state: "A",
    b: { value: 1 }
  };
  const correction = "A";

  const formula = correctOne(transAst, parameterMap, trace, correction);
  expect(formula).toBe('(= "A" (ite (> 1 (+ 0 delta_paramA)) "B" "A"))');
});

test("correctOne - nested", () => {
  const transAst = jsParser.parse(`
if (state == 'A') {
  if (input > paramA) {
    return 'B';
  } else {
    return 'A';
  }
} else {
  return 'C';
}
`);
  const parameterMap = {
    paramA: 0
  };
  const trace = {
    state: "A",
    input: 1
  };
  const correction = "A";

  const formula = correctOne(transAst, parameterMap, trace, correction);
  console.log(formula);
  expect(formula).toBe('(= "A" (ite (> 1 (+ 0 delta_paramA)) "B" "A"))');
});

test("createSRTRSMT2 - transition function", () => {
  const transAst = jsParser.parse(`
if (state == 'A' && b.value > paramA) {
  return 'B';
} else if (state == 'B' && b.value <= paramA) {
  return 'A';
} else {
  return state;
}
`);
  const parameterMap = {
    paramA: 2
  };
  const traces = [
    {
      stamp: 0,
      trace: {
        state: "A",
        b: { value: 1 }
      }
    },
    {
      stamp: 1,
      trace: {
        state: "B",
        b: { value: -1 }
      }
    }
  ];
  const corrections = [
    {
      stamp: 0,
      state: "B"
    },
    {
      stamp: 1,
      state: "A"
    }
  ];
  const options = { H: 1 };

  const formula = createSRTRSMT2(
    transAst,
    parameterMap,
    traces,
    corrections,
    options
  );
  expect(formula).toBe(`(define-fun absolute ((x Real)) Real
  (ite (>= x 0) x (- x)))(declare-const w0 Real)
(declare-const w1 Real)
(declare-const delta_paramA Real)
(assert (and (and true (xor (= w0 1) (and (= w0 0) (= "B" (ite (> 1 (+ 2 delta_paramA)) "B" "A"))))) (xor (= w1 1) (and (= w1 0) (= "A" (ite (<= -1 (+ 2 delta_paramA)) "A" "B"))))))
(minimize (+ w0 w1 (absolute delta_paramA)))
(check-sat)
(get-model)
`);
});

test("createSRTRSMT2 - unsat-able traces", () => {
  const transAst = jsParser.parse(`
if (state == 'A' && input > paramA) {
  return 'B';
} else {
  return state;
}
`);
  const parameterMap = {
    paramA: 0
  };
  const traces = [
    {
      stamp: 0,
      trace: {
        state: "A",
        input: 1
      }
    },
    {
      stamp: 1,
      trace: {
        state: "A",
        input: 1.5
      }
    },
    {
      stamp: 2,
      trace: {
        state: "A",
        input: 0.5
      }
    },
    {
      stamp: 3,
      trace: {
        state: "A",
        input: -1
      }
    },
    {
      stamp: 4,
      trace: {
        state: "A",
        input: -1
      }
    },
    {
      stamp: 5,
      trace: {
        state: "A",
        input: -1.5
      }
    },
    {
      stamp: 6,
      trace: {
        state: "A",
        input: -0.5
      }
    },
    {
      stamp: 7,
      trace: {
        state: "A",
        input: 1
      }
    }
  ];
  const corrections = [
    {
      stamp: 0,
      state: "B"
    },
    {
      stamp: 1,
      state: "B"
    },
    {
      stamp: 2,
      state: "B"
    },
    {
      stamp: 3,
      state: "B"
    },
    {
      stamp: 4,
      state: "A"
    },
    {
      stamp: 5,
      state: "A"
    },
    {
      stamp: 6,
      state: "A"
    },
    {
      stamp: 7,
      state: "A"
    }
  ];
  const options = { H: 1 };

  const formula = createSRTRSMT2(
    transAst,
    parameterMap,
    traces,
    corrections,
    options
  );
  expect(formula).toBe(`(define-fun absolute ((x Real)) Real
  (ite (>= x 0) x (- x)))(declare-const w0 Real)
(declare-const w1 Real)
(declare-const w2 Real)
(declare-const w3 Real)
(declare-const w4 Real)
(declare-const w5 Real)
(declare-const w6 Real)
(declare-const w7 Real)
(declare-const delta_paramA Real)
(assert (and (and (and (and (and (and (and (and true (xor (= w0 1) (and (= w0 0) (= "B" (ite (> 1 (+ 0 delta_paramA)) "B" "A"))))) (xor (= w1 1) (and (= w1 0) (= "B" (ite (> 1.5 (+ 0 delta_paramA)) "B" "A"))))) (xor (= w2 1) (and (= w2 0) (= "B" (ite (> 0.5 (+ 0 delta_paramA)) "B" "A"))))) (xor (= w3 1) (and (= w3 0) (= "B" (ite (> -1 (+ 0 delta_paramA)) "B" "A"))))) (xor (= w4 1) (and (= w4 0) (= "A" (ite (> -1 (+ 0 delta_paramA)) "B" "A"))))) (xor (= w5 1) (and (= w5 0) (= "A" (ite (> -1.5 (+ 0 delta_paramA)) "B" "A"))))) (xor (= w6 1) (and (= w6 0) (= "A" (ite (> -0.5 (+ 0 delta_paramA)) "B" "A"))))) (xor (= w7 1) (and (= w7 0) (= "A" (ite (> 1 (+ 0 delta_paramA)) "B" "A"))))))
(minimize (+ w0 w1 w2 w3 w4 w5 w6 w7 (absolute delta_paramA)))
(check-sat)
(get-model)
`);
});
