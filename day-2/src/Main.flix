use Core/IO/File.readLines;
use Core/Result.Err;

enum Move {
  case Forward(Int32)
  case Down(Int32)
  case Up(Int32)
}

def part1(moves: List[Move]): Int32 = {
    let (x, y) = List.foldLeft((pos, move) -> match (pos, move) {
        case ((x, y), Forward(d)) => (x + d, y)
        case ((x, y), Up(d)) => (x, y - d)
        case ((x, y), Down(d)) => (x, y + d)
    }, (0, 0), moves);

    x * y
}

type alias SubState = { x :: Int32, y :: Int32, aim :: Int32 }

def makeMove(state: SubState, move: Move): SubState = match move {
    case Forward(d) => ({ x = state.x + d, y = state.y + (state.aim * d) | state })
    case Up(d) => ({ aim = state.aim - d | state })
    case Down(d) => ({ aim = state.aim + d | state })
}

def part2(moves: List[Move]): Int32 = {
    let state = List.foldLeft(makeMove, { x = 0, y = 0, aim = 0}, moves);

    state.x * state.y
}


def parseLine(label: String, ctor: Int32 -> Move, line: String): Option[Move] = {
    String.stripPrefix({ substr = label }, line)
    |> Option.flatMap(rest -> Result.toOption(Int32.fromString(rest)))
    |> Option.map(ctor)
}

def parse(line: String): Result[Move, String] = {
    let parsed = parseLine("forward", Forward, line)
    |> Option.withDefault(parseLine("up", Up, line))
    |> Option.withDefault(parseLine("down", Down, line));

    Option.toOk(parsed, "Invalid label")
}

// The main entry point.
def main(_args: Array[String]): Int32 & Impure =
  let linesResult = File.readLines("input.txt")
    |> Result.flatMap(lines -> Result.traverse(parse, lines));

  match linesResult {
    case Ok(lines)  => {
      println("part 1: ${part1(lines)}");
      println("part 2: ${part2(lines)}")
    }
    case Err(msg)   => print("Error ${msg}")
  };
  0 // exit code
