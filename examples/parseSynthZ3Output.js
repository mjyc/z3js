const readline = require("readline");
const { fromSMT2, sexpParser } = require("../");

const rl = readline.createInterface({
  input: process.stdin,
  output: process.stdout,
  terminal: false
});

const lines = [];
rl.on("line", line => {
  lines.push(line);
  if (lines.length === 9) {
    const z3Output = lines.slice(1).join("\n");
    console.log(JSON.stringify(fromSMT2(sexpParser.parse(z3Output)), null, 2));
  }
});
