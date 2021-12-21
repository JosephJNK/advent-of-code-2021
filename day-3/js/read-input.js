const fs = require('fs');

const input = fs.readFileSync("./input", "utf8")
  .split("\n").map(s => s.split(""));

function read(row, column) {
  return input[row][column];
}

exports.read = read;