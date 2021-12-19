module {:extern "ProblemInput", "./js/read-input"} ProblemInput {
  method {:extern "read"} Read() returns (s: array2<string>)
}

method Main() {
  var input := ProblemInput.Read();
  print input;
}