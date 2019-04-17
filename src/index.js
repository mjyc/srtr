"use strict";

function astRemoveNode(ast, pred) {
  function filter(ast) {
    if (!pred(ast)) {
      return null;
    }

    return Object.keys(ast).reduce(function(prev, k) {
      if (Array.isArray(ast[k])) {
        prev[k] = ast[k]
          .map(function(elem) {return filter(elem);})
          .filter(function(elem) {return elem !== null});
      } else if (typeof ast[k] === 'object' && ast[k] !== null) {
        var t = filter(ast[k]);
        if (t !== null) {
          prev[k] = t;
        }
      } else {
        prev[k] = ast[k];
      }
      return prev;
    }, {});
  }

  return filter(ast);
}

function astToJS(ast) {
  if (ast.type === 'Identifier') {
    return ast.name;
  } else if (ast.type === 'UnaryExpression') {
    return `(${ast.operator} ${astToJS(ast.argument)})`;
  } else if (ast.type === 'BinaryExpression') {
    return `(${astToJS(ast.left)} ${ast.operator} ${astToJS(ast.right)})`;
  } else if (ast.type === 'LogicalExpression') {
    return `(${astToJS(ast.left)} ${ast.operator} ${astToJS(ast.right)})`;
  } else if (ast.type === 'ExpressionStatement') {
    return `${astToJS(ast.expression)}`;
  } else if (ast.type === 'Literal') {
    return `${typeof ast.value === 'string' ? JSON.stringify(ast.value) : ast.value}`;
  } else if (ast.type === 'ReturnStatement') {
    return `return ${astToJS(ast.argument)}`;
  } else if (ast.type === 'BlockStatement') {
    return ast.body.map(function(b) {return `${astToJS(b)};`;}).join(' ');
  } else if (ast.type === 'IfStatement') {
    return `if (${astToJS(ast.test)}) { ${astToJS(ast.consequent)} } else { ${astToJS(ast.alternate)} }`;
  } else if (ast.type === 'MemberExpression') {
    return `${astToJS(ast.object)}["${astToJS(ast.property)}"]`;
  } else if (ast.type === 'Property') {
    return `"${astToJS(ast.key)}": ${astToJS(ast.value)}`;
  } else if (ast.type === 'ObjectExpression') {
    return `{${ast.properties.map(function (property) {return astToJS(property);}).join(', ')}}`;
  } else if (ast.type === 'Program') {
    return ast.body.map(function (b) {return astToJS(b);}).join(' ');
  } else {
    throw new Error(`Invalid input ast=${JSON.stringify(ast)}`);
  }
}

function subsituteVariables(ast, variableMap) {
  function subsitute(ast, varMap) {
    if (ast.type === 'Identifier') {
      var value = varMap[ast.name];
      return typeof value === 'undefined' ? ast
        : {
          type: 'Literal',
          value: value,
        };
    } else if (ast.type === 'MemberExpression') {
      const object = subsitute(ast.object, varMap);
      const property = !ast.property.computed
        ? ast.property : subsitute(ast.property, varMap);
      return (typeof object.value === 'object' && object.value !== null)
        ? subsitute(
          property.type === 'Literal'
            ? {
              type: 'Identifier',
              name: property.value
            } : property,
          object.value
        ) : ast;
    }

    return Object.keys(ast).reduce(function(prev, k) {
      if (Array.isArray(ast[k])) {
        prev[k] = ast[k]
          .map(function(elem) {return subsitute(elem, varMap);});
      } else if (typeof ast[k] === 'object' && ast[k] !== null) {
        prev[k] = subsitute(ast[k], varMap);
      } else {
        prev[k] = ast[k];
      }
      return prev;
    }, {});
  }

  return subsitute(ast, variableMap);
}

function extractVariables(ast) {
  function extract(ast, vars) {
    if (ast.type === 'Identifier') {
      return vars.slice(0).concat(ast.name);
    } else if (ast.type === 'MemberExpression') {
      const objVars = extractVariables(ast.object, vars);
      const propVars = !ast.property.computed
        ? [] : extractVariables(ast.property, vars);
      return objVars.concat(propVars);
    }

    return Object.keys(ast).reduce(function(prev, k) {
      if (Array.isArray(ast[k])) {
        return prev.concat(
          ast[k]
            .map(function(elem) {return extract(elem, vars);})
            .reduce(function (prev, arr) { return prev.concat(arr); }, vars)
        );
      } else if (typeof ast[k] === 'object' && ast[k] !== null) {
        return prev.concat(extract(ast[k], vars));
      } else {
        return prev;
      }
    }, []);
  }

  var vars = extract(ast, []);
  return vars.filter(function(v, i){ return vars.indexOf(v) >= i; });
}

function makeResidual(transAst, paramMap, trace) {

<<<<<<< HEAD
  var ast = subsituteVariables(
    subsituteVariables(transAst, paramMap),
    trace,
  );
  console.log(astToJS(ast));
=======
//   function pEval(ast) {
//     if (ast.type === 'IfStatement') {

//       try {
//         Function(`
// "use strict";
// return function() {
// ${paramMapToJS(paramMap)}
// return ${astToJS(ast.test)};
// }()`)();
//       } catch (e) {
//         ast.consequent
//       }

//     }
//   }

  // subsituteVariables(transAst, )


  // var ast = subsituteVariables(
  //   subsituteVariables(transAst, paramMap),
  //   trace,
  // );
  // console.log(ast);
>>>>>>> c5ee426... WIP

//   function paramMapToJS(pMap) {
//     return Object.keys(pMap).map(function(k) {
//       return `var ${k} = ${JSON.stringify(pMap[k])};`
//     }).join('\n');
//   }

  function selectSubtree(ast) {
    if (ast.type === 'ReturnStatement') {
      return ast.argument;
    } else if (ast.type === 'BlockStatement') {
      if (ast.body.length > 1) {
        throw new Error(`BlockStatement is not supported for ast.body.length=${ast.body.length} > 1`);
      }
      return ast.body.map(function(b) {return selectSubtree(b);})[0];
    } else if (ast.type === 'IfStatement') {
      var testVal = Function(`
"use strict";
return function() {
return ${astToJS(ast.test)};
}()`)();
      return testVal
        ? selectSubtree(ast.consequent)
        : selectSubtree(ast.alternate);
    } else {
      throw new Error(`Invalid input ast=${JSON.stringify(ast)}`);
    }
  }

//   return selectSubtree(transAst);
  return undefined;
}

function correctOne(transAst, paramMap, trace, correction) {

  // paramMap should ... ?
  // var residual = makeResidual(transAst, paramMap);


  // function paramMapToJS(pMap) {
  //   return Object.keys(pMap).map(function(k) {
  //     return `var ${k} = ${JSON.stringify(pMap[k])};`
  //   }).join('\n');
  // }
  // // combine trace & correction to create parameters to transition-args
  // // create args that will be used in (transition ${}) from combined thing
  // `(= ${correction} (transition ${}))`
  return undefined;
}

function correctAll(transAst, paramMap, trace, corrections) {
  return undefined;
}

function srtr(transAst, paramMap, trace, corrections) {
  return undefined;
}

module.exports = {
  astRemoveNode: astRemoveNode,
  astToJS: astToJS,
  subsituteVariables: subsituteVariables,
  extractVariables: extractVariables,
  makeResidual: makeResidual,
}
