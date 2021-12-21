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

function method minus1(x: int): int { x - 1 }

method twoDArrayToRows<T>(arr: array2<T>)
  returns (result: array<array<T>>)
  requires arr.Length0 > 0
  requires arr.Length1 > 0
  ensures result.Length == arr.Length1
  ensures forall i :: 0 <= i < result.Length ==> result[i].Length == arr.Length0
  ensures forall i, j :: 0 <= i < arr.Length1 && 0 <= j < arr.Length0 ==>
      result[i][j] == arr[j, i]
  {
    var temp := new array<T>[arr.Length1];

    temp[0] := new T[arr.Length0](j
        reads arr
        requires 0 <= j < arr.Length0 => arr[j, 0]);

    assert temp[0].Length == arr.Length0;

    var i := 0;

    assert forall j :: 0 <= j < arr.Length0 ==> temp[0][j] == arr[j, 0];

    while i < minus1(arr.Length1) && i < minus1(temp.Length)
      invariant 0 <= i < arr.Length1
      invariant temp.Length == arr.Length1
      invariant 0 <= i < temp.Length
      invariant temp[i].Length == arr.Length0
      invariant temp[0].Length == arr.Length0
      invariant forall x :: 0 <= x < i ==> temp[x].Length == arr.Length0;
      invariant forall j :: 0 < j < temp[i].Length ==> temp[i][j] == arr[j, i]
      invariant forall x, j :: 0 <= x < i && 0 < j < arr.Length0
          ==> temp[x][j] == arr[j, x]
      invariant forall j :: 0 < j < temp[0].Length ==> temp[0][j] == arr[j, 0];
      {
        ghost var beforeUpdate := temp[0];
        assert forall j :: 0 < j < temp[0].Length ==> temp[0][j] == arr[j, 0];
        assert forall j :: 0 < j < temp[0].Length ==> beforeUpdate[j] == arr[j, 0];

        i := i + 1;
        assert i > 0;
        temp[i] := new T[arr.Length0](j
          reads arr
          requires 0 <= j < arr.Length0 => arr[j, i]);
        
        assert temp[0] == beforeUpdate;

        assert forall j :: 0 < j < arr.Length0 ==> temp[0][j] == arr[j, 0];
        assert forall j :: 0 < j < temp[0].Length ==> temp[0][j] == arr[j, 0];
        assert forall j :: 0 < j < temp[i].Length ==> temp[i][j] == arr[j, i];
        assert forall j :: 0 < j < arr.Length0 ==> temp[i][j] == arr[j, i];
        assert forall x, j :: 0 <= x < i && 0 < j < arr.Length0
            ==> temp[x][j] == arr[j, x];
      }
    assert i == arr.Length1 - 1;
    assert temp[i].Length == arr.Length0;
    assert temp[0].Length == arr.Length0;
    assert forall j :: 0 < j < arr.Length0 ==> temp[i][j] == arr[j, i];
    assert forall i :: 0 <= i < temp.Length ==> temp[i].Length == arr.Length0;

    result := temp;
    assert result.Length == temp.Length;
    assert forall i :: 0 <= i < result.Length ==> result[i] == temp[i];
    assert forall i, j :: 0 <= i < arr.Length1 && 0 <= j < arr.Length0 ==>
      result[i][j] == temp[i][j];

  }

datatype Bit = Zero | One

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
