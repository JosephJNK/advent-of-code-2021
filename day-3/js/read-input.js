const fs = require('fs');

function read() {
  const input = fs.readFileSync("./input", "utf8");
  return input.split("\n").map(s => s.split());
}

exports.read = read;