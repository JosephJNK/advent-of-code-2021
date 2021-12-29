include "IList.dfy"

module Parsing {
  import IList

  export
  reveals OneParse, Result, parser
  provides fmap, IList

  datatype OneParse<T> = OneParse(parsed: T, remainder: string)
  datatype Result<T> = Failure | Success(forest: IList.IList<OneParse>)

  type parser<T> = string -> Result<T>

  greatest predicate ParseResultForall<T>(result: Result<T>, pred: T -> bool) {
    match result
    case Failure => true
    case Success(forest) => IList.IListForall(forest,
      (one: OneParse) => pred(one.parsed))
  }

  greatest predicate ParserForall<T>(p: parser<T>, fn: T -> bool) {
    forall s :: ParseResultForall(p(s), fn)
  }

  function method fmapSuccess<S, T>(result: Result<S>, fn: S -> T): Result<T>
    requires result.Success?
    {
      var innerFn :=
        (one: OneParse<S>)
        requires fn.requires(one.parsed)
        => OneParse(fn(one.parsed), one.remainder);
      Success(IList.fmap(result.forest, innerFn))
    }

  function method fmap<T, U>(p: parser<T>, fn: T -> U): parser<U>
    {
      s => 
        var result := p(s);
        match result
        case Failure => Failure
        case Success(_) => fmapSuccess(result, fn)
    }

  function method success<T>(
    result: T, remainder: string, ghost pred: T -> bool): Result<T>
    requires pred(result)
    ensures ParseResultForall(success(result, remainder, pred), pred)
    {
      ghost var liftedPred := (op: OneParse<T>) => pred(op.parsed);
      Success(IList.of(OneParse(result, remainder), liftedPred))
    }

  function method fail<T>(ghost pred: T -> bool): Result<T>
  ensures ParseResultForall(fail(pred), pred)
  { Failure }

  function method character(c: char): parser<char>
  ensures ParserForall(character(c), x => x == c) {
    s =>
      if |s| == 0 then fail(x => x == c)
      else if s[0] == c then success(c, s[1..], x => x == c)
      else fail(x => x == c)
  }

  function method charClass(cs: set<char>): parser<char>
  ensures ParserForall(charClass(cs), x => x in cs)
  {
    s =>
      if |s| == 0 then fail(x => x in cs)
      else if s[0] in cs then success(s[0], s[1..], x => x in cs)
      else fail(x => x in cs)
  }

  const digits: set<char> := {
    '0', '1', '2', '3', '4', '5', '6', '7', '8', '9'};

  function method digit(): parser<char>
  ensures ParserForall(digit(), x => x in digits)
  {
    assert ParserForall(charClass(digits), x => x in digits);
    charClass(digits)
  }
}