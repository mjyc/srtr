const {parser} = require('js2smt2');
const {
  astToJS,
  subsituteVariables,
  pEval,
  extractVariables,
  correctOne,
  correctAll,
  createSRTRSMT2,
} = require('./');

const transAst = parser.parse(`
if (
  state === "S1" &&
  inputD["type"] === "Features" &&
  inputC["face"]["faceCenterX"] > params["engagedMinX"]
) {
  return "S2";
} else {
  if (
    state === "S2" &&
    inputD["type"] === "Features" &&
    inputC["face"]["faceCenterX"] < params["engagedMinX"]
  ) {
    return "S1";
  } else {
    return state;
  }
}
`);

const parameterMap = {
  engagedMinX: 340,
};

const trace = {
  state: 'S1',
  inputD: {
    type: "Features",
  },
  inputC: {
    face: {
      faceCenterX: 200
    },
  },
}

const correction = 'S2';

const formula = correctOne(transAst, parameterMap, trace, correction);

console.log(formula);
