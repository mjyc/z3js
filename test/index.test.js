const {
  toSMT2,
  fromSMT2,
  jsParser,
  sexpParser,
  declareDatatypes
} = require("../src/");

test("toSMT2", () => {
  const ast = jsParser.parse(`
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
`);
  const typeLookup = {
    x: "String",
    y: "(B String Int)",
    f: {
      a: "String",
      b: "(B String Int)",
      return: "String"
    }
  };

  expect(toSMT2(ast, typeLookup)).toBe(`(declare-const x String)
(declare-const y (B String Int))
(define-fun f ((a String) (b (B String Int))) String (ite (and (and (= a "hello") (= (type b) "there")) (= (* (value b) 1) 0)) "branch1" (ite (and (and (= a "jello") (= (type b) "whirl")) (= (+ (value b) 1) 2)) "branch2" "branch3")))
(assert (= (f x y) "branch2"))`);
});

test("toSMT2 - fncKeywords", () => {
  expect(toSMT2(jsParser.parse(`check_sat()`))).toBe(`(check-sat )`);
  expect(toSMT2(jsParser.parse(`get_model()`))).toBe(`(get-model )`);
});

test("toSMT2 - forall", () => {
  expect(
    toSMT2(jsParser.parse(`forall(x, x * 2 == 2 * x)`), { x: "Int" })
  ).toBe(`(forall ((x Int)) (= (* x 2) (* 2 x)))`);
});

test("fromSMT2", () => {
  const SEXP_CODE = `(model
  (define-fun y () Int
    1)
  (define-fun x () String
    "jello")
)`;
  const ast = sexpParser.parse(SEXP_CODE);
  expect(fromSMT2(ast)).toEqual({
    x: "jello",
    y: 1
  });
});

test("declareDatatypes", () => {
  expect(
    declareDatatypes("JSObj", {
      type: "String",
      value: "Int"
    })
  ).toBe(`(declare-datatypes () ((JSObj (jsobj (type String) (value Int)))))`);
});
