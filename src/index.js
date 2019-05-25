"use strict";

const jsParser = require("./javascript-parser.js");
const sexpParser = require("./s-expression-parser.js");

const uopToSMT = {
  "-": "-",
  "+": "+",
  "!": "not"
};

const bopToSMT = {
  "===": "=",
  // '!==': undefined,
  "==": "=",
  // '!=': undefined,
  "<": "<",
  "<=": "<=",
  ">": ">",
  ">=": ">=",
  "+": "+",
  "-": "-",
  "*": "*"
  // '**': '^',
  // '/': 'div',
  // '%': 'mod',
};

const lopToSMT = {
  "||": "or",
  "&&": "and"
};

const fncKeywords = {
  check_sat: "check-sat",
  get_model: "get-model"
};

function interpret(ast, typeLookup) {
  if (ast.type === "Identifier") {
    return `${ast.name}`;
  } else if (ast.type === "UnaryExpression") {
    return `(${uopToSMT[ast.operator]} ${interpret(ast.argument, typeLookup)})`;
  } else if (ast.type === "BinaryExpression") {
    return `(${bopToSMT[ast.operator]} ${interpret(
      ast.left,
      typeLookup
    )} ${interpret(ast.right, typeLookup)})`;
  } else if (ast.type === "LogicalExpression") {
    return `(${lopToSMT[ast.operator]} ${interpret(
      ast.left,
      typeLookup
    )} ${interpret(ast.right, typeLookup)})`;
  } else if (ast.type === "ExpressionStatement") {
    return `${interpret(ast.expression, typeLookup)}`;
  } else if (ast.type === "Literal") {
    switch (typeof ast.value) {
      case "boolean":
        return ast.value;
      case "number":
        return ast.value;
      case "string":
        return JSON.stringify(ast.value);
      default:
        throw new Error(`Invalid typeof ast.value=${typeof ast.value}`);
    }
  } else if (ast.type === "ReturnStatement") {
    return `${interpret(ast.argument, typeLookup)}`;
  } else if (ast.type === "BlockStatement") {
    if (ast.body.length > 1) {
      throw new Error(
        `BlockStatement is not supported for ast.body.length=${
          ast.body.length
        } > 1`
      );
    }
    return ast.body
      .map(function(b) {
        return `${interpret(b, typeLookup)}`;
      })
      .join(" ");
  } else if (
    ast.type === "IfStatement" ||
    ast.type === "ConditionalExpression"
  ) {
    if (ast.alternate == null) {
      throw new Error(
        `ast.alternate must be provided for IfStatement; ast=${JSON.stringify(
          ast
        )}`
      );
    }
    return `(ite ${interpret(ast.test, typeLookup)} ${interpret(
      ast.consequent,
      typeLookup
    )} ${interpret(ast.alternate, typeLookup)})`;
  } else if (ast.type === "MemberExpression") {
    return `(${interpret(ast.property, typeLookup)} ${interpret(
      ast.object,
      typeLookup
    )})`;
  } else if (ast.type === "FunctionDeclaration") {
    const id = interpret(ast.id, typeLookup);
    const tLookup = typeLookup[id];
    if (typeof tLookup === "undefined") {
      throw Error(
        `Type for function ${id} must be provided; typeLookup=${JSON.stringify(
          typeLookup
        )}`
      );
    }
    const params = ast.params.map(function(param) {
      const p = interpret(param, typeLookup);
      if (typeof tLookup[p] === "undefined") {
        throw Error(
          `Type for function ${id}'s argument ${p} must be provided; typeLookup=${JSON.stringify(
            typeLookup
          )}`
        );
      }
      return { type: tLookup[p], value: p };
    });
    const tReturn = tLookup.return;
    if (typeof tReturn === "undefined") {
      throw Error(
        `Type for function "${id}"'s return value must be provided; typeLookup=${JSON.stringify(
          typeLookup
        )}`
      );
    }
    return `(define-fun ${interpret(ast.id, typeLookup)} (${params
      .map(function(param) {
        return `(${param.value} ${param.type})`;
      })
      .join(" ")}) ${tReturn} ${interpret(ast.body, typeLookup)})`;
  } else if (ast.type === "VariableDeclarator") {
    const id = interpret(ast.id, typeLookup);
    const tLookup = typeLookup[id];
    if (typeof tLookup === "undefined") {
      throw Error(
        `Type for variable ${id} must be provided; typeLookup=${JSON.stringify(
          typeLookup
        )}`
      );
    }
    if (ast.init !== null) {
      throw Error(
        `Cannot store value ${ast.init} when declarating variable ${id}`
      );
    }
    return `(declare-const ${id} ${tLookup})`;
  } else if (ast.type === "VariableDeclaration") {
    return ast.declarations
      .map(function(declaration) {
        return `${interpret(declaration, typeLookup)}`;
      })
      .join("\n");
  } else if (ast.type === "CallExpression") {
    let callee = interpret(ast.callee, typeLookup);
    callee = !!fncKeywords[callee] ? fncKeywords[callee] : callee;
    return `(${callee} ${ast.arguments
      .map(function(argument, i) {
        const arg = interpret(argument, typeLookup);
        if (
          callee === "forall" &&
          i === 0 &&
          typeof typeLookup[arg] === "undefined"
        ) {
          throw Error(
            `Type for variable ${arg} must be provided; typeLookup=${JSON.stringify(
              typeLookup
            )}`
          );
        }
        return callee === "forall" && i === 0
          ? `((${arg} ${typeLookup[arg]}))`
          : arg;
      })
      .join(" ")})`;
  } else if (ast.type === "Program") {
    return ast.body.map(s => interpret(s, typeLookup)).join("\n");
  } else {
    throw Error(
      `Invalid input ast=${JSON.stringify(ast)}; returning an empty string;`
    );
  }
}

function toSMT2(ast, typeLookup) {
  const tLookup = typeof typeLookup === "undefined" ? {} : typeLookup;
  return interpret(ast, tLookup);
}

function fromSMT2(tree) {
  const interp = ast => {
    if (ast.type === "Literal") {
      return ast.value;
    } else if (ast.type === "Identifier") {
      return ast.name;
    } else if (ast.type === "Atom") {
      return interp(ast.value);
    } else if (ast.type === "Expression") {
      const values = ast.value.map(interp);
      if (values[0] === "define-fun") {
        return { [values[1]]: values[4] };
      } else if (values[0] === "model") {
        return values.slice(1).reduce(function(acc, x) {
          Object.keys(x).map(function(k) {
            acc[k] = x[k];
          });
          return acc;
        });
      } else {
        console.warn(`Invalid ast.values[0]=${values[0]}; retunring null`);
        return null;
      }
    }
  };
  return interp(tree);
}

function declareDatatypes(typeName, typeDefs) {
  return `(declare-datatypes () ((${typeName} (jsobj ${Object.keys(typeDefs)
    .map(function(key, i) {
      return `(${key} ${typeDefs[key]})`;
    })
    .join(" ")}))))`;
}

module.exports = {
  interpret: interpret,
  toSMT2: toSMT2,
  fromSMT2: fromSMT2,
  declareDatatypes: declareDatatypes,
  jsParser: jsParser,
  sexpParser: sexpParser
};
