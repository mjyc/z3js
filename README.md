# z3js

A tiny utility library for building z3-powered JavaScript.

The main features are:

* A transpiler for converting a _tiny_ subset of JavaScript programs to [smt2](http://smtlib.cs.uiowa.edu/logics.shtml) to use [z3 solver](https://rise4fun.com/z3/tutorial).
* A _tiny_ s-expression parser for reading z3 outputs in smt2 to JavaScript objects.

## Examples

Create a file `demo.js` and add:

```
const { jsParser, toSMT2, declareDatatypes } = require("z3js"); // or "path/to/z3js/src"

const JS_CODE = `
var x;

function f(args) {
  return args.one * args.two;
}

assert(f(x) === 2);
check_sat();
get_model();
`;

const typeDefs = {
  x: "(Arg)",
  y: "(Arg)",
  f: {
    args: "(Arg)",
    return: "Int"
  }
};

console.log(`
${declareDatatypes("Arg", { one: "Int", two: "Int" })}
${toSMT2(jsParser.parse(JS_CODE), typeDefs)}
`);
```

and run `node demo.js | z3 -in`. You'll need [z3](https://github.com/Z3Prover/z3), which you can install by running `brew install z3` or `sudo apt install z3` on Mac or Ubuntu, respectively.

### Reading Z3 outputs

Try

```
node examples/synth.js | z3 -in | node examples/parseSynthZ3Output.js
```

and check out [`./examples/parseSynthZ3Output.js`](./examples/parseSynthZ3Output.js).

### Program Synthesis demo

Check out [`./examples/synth.js`](./examples/synth.js)! The demo code is loosely based on [Adrian Sampson]()'s [program synthesis blog post](https://www.cs.cornell.edu/~asampson/blog/minisynth.html).


## Inspired by

* [@stanford-oval's node-smtlib](https://github.com/stanford-oval/node-smtlib)
* [@levjj's esverify](https://github.com/levjj/esverify)
* [@cpitclaudel's z3.wasm](https://github.com/cpitclaudel/z3.wasm)
* [@emina's rosette](https://github.com/emina/rosette)
* ["Program Synthesis is Possible"](https://www.cs.cornell.edu/~asampson/blog/minisynth.html) by Adrian Sampson
