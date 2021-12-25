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
function method plus1(x: int): int { x + 1 }

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
      fn(arr[i]) == true ==> contains?(result, arr[i]) {

        if (arr.Length == 0) {
          result := new T[0];
          return;
        }

        var arraySize := 0;
        var filteredSeq : seq<T> := [];

        for i := 0 to arr.Length
        invariant |filteredSeq| == arraySize
        invariant arraySize <= arr.Length
        invariant arraySize <= i
        invariant forall i | 0 <= i < |filteredSeq| :: fn(filteredSeq[i]) == true
        invariant forall i | 0 <= i < |filteredSeq| :: 
            contains?(arr, filteredSeq[i])
        invariant forall j | 0 <= j < i :: 
            fn(arr[j]) == true ==> arr[j] in filteredSeq
        {
          if (fn(arr[i])) {
            arraySize := arraySize + 1;
            filteredSeq := filteredSeq + [arr[i]];
          }
        }

        assert forall i | 0 <= i < arr.Length :: 
            fn(arr[i]) == true ==> arr[i] in filteredSeq;

        result := new T[|filteredSeq|](
          i requires 0 <= i < |filteredSeq| => filteredSeq[i]);

        assert forall i | 0 <= i < |filteredSeq| :: result[i] == filteredSeq[i];
        assert forall t :: t in filteredSeq ==> contains?(result, t);
      }

function flattenSeq<T>(s: seq<set<T>>): set<T> {
  if |s| == 0 then {} else s[0] + flattenSeq(s[1..])
}

function method filterSeq<T>(s: seq<T>, fn: T --> bool): seq<T>
  requires forall x | x in s :: fn.requires(x)
  ensures forall x | x in filterSeq(s, fn) :: x in s
  ensures forall i | 0 <= i < |filterSeq(s, fn)| :: fn(filterSeq(s, fn)[i]) == true
  ensures forall i | 0 <= i < |filterSeq(s, fn)| :: filterSeq(s, fn)[i] in s
  ensures forall i | 0 <= i < |s| :: fn(s[i]) ==> s[i] in filterSeq(s, fn)
  {
    if |s| == 0 then [] else (
      if fn(s[0]) then [s[0]] + filterSeq(s[1..], fn) else filterSeq(s[1..], fn)
    )
  }

method twoDArrayToSeqOfSeqs<T>(arr: array2<T>)
  returns (result: seq<seq<T>>)
  ensures |result| == arr.Length1
  ensures forall i | 0 <= i < arr.Length1 :: |result[i]| == arr.Length0
  ensures forall i, j | 0 <= i < arr.Length1  && 0 <= j < arr.Length0
      :: result[i][j] == arr[j, i]
  {
    result := [];
    for i := 0 to arr.Length1
    invariant |result| == i
    invariant forall x | 0 <= x < i :: |result[x]| == arr.Length0
    invariant forall x, j | 0 <= x < i && 0 <= j < arr.Length0
        :: result[x][j] == arr[j, x]
    {
      var line := [];

      for j := 0 to arr.Length0
      invariant |line| == j
      invariant forall x | 0 <= x < j :: line[x] == arr[x, i]
      {
        line := line + [arr[j, i]];
      }

      result := result + [line];
    }
  }


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

function method bin2DecSeq'(binary: seq<Bit>, acc: nat): nat {
  if |binary| == 0 then acc
  else if binary[0] == One then bin2DecSeq'(binary[1..], acc * 2 + 1)
  else bin2DecSeq'(binary[1..], acc * 2)
}

function method bin2DecSeq(binary: seq<Bit>): nat {
  bin2DecSeq'(binary, 0)
}

// test
lemma bin2DecSeq6() ensures bin2DecSeq([One, One, Zero]) == 6 {}
lemma bin2DecSeq6'() ensures bin2DecSeq([Zero, One, One, Zero]) == 6 {}

method getMostCommonBitAtIndex(i: nat, s: seq<seq<Bit>>)
  returns (result: Bit)
  requires forall row | row in s :: i < |row|
  {
    var onesCount := 0;

    for j := 0 to |s| {
      var row := s[j];
      if (row[i] == One) {
        onesCount := onesCount + 1;
      }
    }

    var zeroesCount := |s| - onesCount;

    if onesCount >= zeroesCount {
      result := One;
    } else {
      result := Zero;
    }
  }

method getLeastCommonBitAtIndex(i: nat, s: seq<seq<Bit>>)
  returns (result: Bit)
  requires forall row | row in s :: i < |row|
  {
    var mostCommon := getMostCommonBitAtIndex(i, s);
    if mostCommon == One {
      result := Zero;
    } else {
      result := One;
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

  var rows := twoDArrayToSeqOfSeqs(asBits);
  var oxygenGen := rows;

  for i := 0 to 12
  invariant |oxygenGen| > 0
  invariant forall row | row in oxygenGen :: |row| == 12
  {
    var targetBit := getMostCommonBitAtIndex(i, oxygenGen);
    var next := filterSeq(oxygenGen,
      s requires |s| == 12 => s[i] == targetBit);
    if |next| == 0 {
      break;
    }

    oxygenGen := next;
  }

  var co2Scrub := rows;

  for i := 0 to 12
  invariant |co2Scrub| > 0
  invariant forall row | row in co2Scrub :: |row| == 12
  {
    var targetBit := getLeastCommonBitAtIndex(i, co2Scrub);
    var next := filterSeq(co2Scrub,
      s requires |s| == 12 => s[i] == targetBit);
    if |next| == 0 {
      break;
    }

    co2Scrub := next;
  }

  var firstOxy := bin2DecSeq(oxygenGen[0]);
  var firstCo2 := bin2DecSeq(co2Scrub[0]);

  print "oxygen generator: ";
  print firstOxy;
  print "\n";
  print "co2 scrubber: ";
  print firstCo2;
  print "\n";
  print "oxygen generator * co2 scrubber: ";
  print firstOxy * firstCo2;
}
