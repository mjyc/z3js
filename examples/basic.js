const { toSMT2, jsParser, declareDatatypes } = require("../");

const JS_CODE = `
var x;
var y;

function f(a, b) {
  if (a == 'hello' && b.type == 'there' && b.value * 1 === 0) {
    return 'branch1';
  } else if (a == 'jello' && b.type == 'whirl' && b.value + 1 === 2) {
    return 'branch2';
  } else {
    return 'branch3';
  }
}

assert(f(x, y) == "branch2");
check_sat();
get_model();
`;

const typeLookup = {
  x: "String",
  y: "JSObj",
  f: {
    a: "String",
    b: "JSObj",
    return: "String"
  }
};

console.log(`
${declareDatatypes("JSObj", {
  type: "String",
  value: "Int"
})}
${toSMT2(jsParser.parse(JS_CODE), typeLookup)}
`);
