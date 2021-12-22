module {:extern "ProblemInput", "./js/read-input"} ProblemInput {
  function method {:extern "read"} Read(row: int, column: int): char
    requires 0 <= row < 1000
    requires 0 <= column < 12
}

method getInput()returns (result: array2<char>)
  ensures result.Length0 == 12
  ensures result.Length1 == 1000 {
    var intermediate := new char[12, 1000];
    for row := 0 to 1000 {
      for column := 0 to 12 {
        intermediate[column, row] := ProblemInput.Read(row, column);
      }
    }
    result := intermediate;
  }

method mapArray<S, T>(arr: array<S>, fn: S -> T)
  returns (result: array<T>)
  ensures result.Length == arr.Length
  ensures forall i :: 0 <= i < arr.Length ==> result[i] == fn(arr[i]) {
    result := new T[arr.Length](i
      reads arr
      requires 0 <= i < arr.Length => fn(arr[i]));
  }

method mapArray2<S, T>(arr: array2<S>, fn: S -> T)
  returns (result: array2<T>)
  ensures result.Length0 == arr.Length0
  ensures result.Length1 == arr.Length1
  ensures forall i, j :: 0 <= i < arr.Length0 && 0 <= j < arr.Length1 ==>
      result[i, j] == fn(arr[i, j]) {
        result := new T[arr.Length0, arr.Length1](
          (i, j)
          reads arr
          requires 0 <= i < arr.Length0
          requires 0 <= j < arr.Length1 => fn(arr[i, j]));
      }

function method minus1(x: int): int { x - 1 }

method twoDArrayToRows<T>(arr: array2<T>)
  returns (result: array<array<T>>)
  ensures result.Length == arr.Length1
  ensures forall i :: 0 <= i < result.Length ==> result[i].Length == arr.Length0
  ensures forall i, j :: 0 <= i < arr.Length1 && 0 <= j < arr.Length0 ==>
      result[i][j] == arr[j, i]
  {
    if arr.Length1 == 0 {
      result := new array<T>[0];
      return;
    }

    result := new array<T>[arr.Length1];

    result[0] := new T[arr.Length0](j
        reads arr
        requires 0 <= j < arr.Length0 => arr[j, 0]);

    var i := 0;

    while i < minus1(arr.Length1) && i < minus1(result.Length)
      // bounds
      invariant 0 <= i < arr.Length1
      invariant 0 <= i < result.Length

      // Length is correct
      invariant result[i].Length == arr.Length0
      invariant forall x :: 0 <= x < i ==> result[x].Length == arr.Length0;

      // Contents are correct
      invariant forall j :: 0 <= j < result[0].Length ==> result[0][j] == arr[j, 0];
      invariant forall x, j :: 0 < x <= i && 0 <= j < arr.Length0 
          ==> result[x][j] == arr[j, x]
      {
        i := i + 1;
        result[i] := new T[arr.Length0](j
          reads arr
          requires 0 <= j < arr.Length0 => arr[j, i]);
      }
  }

predicate contains?<T>(arr: array<T>, item: T)
  reads arr {
    exists i | 0 <= i < arr.Length :: arr[i] == item
  }

method filterArray<T>(arr: array<T>, fn: T -> bool)
  returns (result: array<T>)
  ensures forall i | 0 <= i < result.Length :: fn(result[i]) == true
  ensures forall i | 0 <= i < result.Length :: contains?(arr, result[i])
  ensures forall i | 0 <= i < arr.Length :: 
      fn(arr[i]) == true ==> contains?(result, arr[i])

datatype Bit = Zero | One

method binaryToDecimal(binary: array<Bit>) returns (result: int) {
  result := 0;

  for i := 0 to binary.Length {
    var bit := binary[i];
    result := result * 2;
    if bit == One {
      result := result + 1;
    }
  }
}

method Main() {
  var input := getInput();
  var asBits := mapArray2(input, s => if s == '0' then Zero else One);
  var columnCounts := new int[12](_ => 0);

  for row := 0 to 1000 {
    for column := 0 to 12 {
      if asBits[column, row] == One {
        columnCounts[column] := columnCounts[column] + 1;
      }
    }
  }

  var gamma := mapArray(columnCounts, n => if n >= 500 then One else Zero);
  var epsilon := mapArray(gamma, x => if x == One then Zero else One);

  var gammaInt := binaryToDecimal(gamma);
  var epsilonInt := binaryToDecimal(epsilon);

  print "gamma: ";
  print gammaInt;
  print "\n";
  print "epsilon: ";
  print epsilonInt;
  print "\n";
  print "gamma * epsilon: ";
  print gammaInt * epsilonInt;
}
