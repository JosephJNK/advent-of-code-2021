const fs = require('fs');

const input = fs.readFileSync("./input", "utf8");

function getInputLength() {
  return input.length;
}

function readChar(index) {
  return input[index];
}

exports.getInputLength = getInputLength;
exports.readChar = readChar;