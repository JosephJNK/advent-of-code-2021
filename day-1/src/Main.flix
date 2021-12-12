use Core/IO/File.readLines;

def countIncreases(
  readings: List[Int32],
  last: Int32,
  increases: Int32): Int32 = match readings {

  case head :: tail => {
    if (head > last)
      countIncreases(tail, head, increases + 1)
    else
      countIncreases(tail, head, increases)
  }
  case Nil => increases
}

def slidingWindow(nums: List[Int32]): List[Int32] = {
  match nums {
    case a :: b :: c :: tail => (a + b + c) :: slidingWindow(b :: c :: tail)
    case _ => Nil
  }
}

def part2(readings: List[Int32]): Int32 = part1(slidingWindow(readings))

def part1(readings: List[Int32]): Int32 = {
  match readings {
    case head :: tail => countIncreases(tail, head, 0)
    case Nil => 0
  }
}

// The main entry point.
def main(_args: Array[String]): Int32 & Impure =
  let linesResult = File.readLines("input.txt")
    |> Result.flatMap(lines -> Result.traverse(Int32.fromString, lines));

  match linesResult {
    case Ok(lines)  => {
      println("part 1: ${part1(lines)}");
      println("part 2: ${part2(lines)}")
    }
    case Err(msg)   => print("Error ${msg}")
  };
  0 // exit code
