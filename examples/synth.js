const { toSMT2, jsParser, declareDatatypes } = require("../");

const JS_CODE = `
var hb1, hb2;
var hn1, hn2;
var x;

function f1(x) {
  return x * 10;
}

function f2(x) {
  return x * (hb1 ? x : hn1) + x * (hb2 ? x : hn2);
}

assert(forall(x, f1(x) === f2(x)));
check_sat();
get_model();
`;

const typeLookup = {
  hb1: "Bool",
  hb2: "Bool",
  hn1: "Int",
  hn2: "Int",
  x: "Int",
  f1: { x: "Int", return: "Int" },
  f2: { x: "Int", return: "Int" }
};

console.log(`
${toSMT2(jsParser.parse(JS_CODE), typeLookup)}
`);
