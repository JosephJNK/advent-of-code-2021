module IList {
  export reveals IList, fmap, IListForall, of

  codatatype IList<T> = Nil | Cons(head: T, tail: IList<T>)

  greatest predicate IListForall<T>(list: IList<T>, fn: T -> bool) {
    match list
    case Nil => true
    case Cons(head, rest) => fn(head) && IListForall(rest, fn)
  }

  function method fmap<S, T>(list: IList<S>, fn: S -> T): IList<T>
  {
    match list
    case Nil => Nil
    case Cons(s, rest) => Cons(fn(s), fmap(rest, fn))
  }

  function method fmapPartial<S, T>(list: IList<S>, fn: S --> T): IList<T>
  requires IListForall(list, fn.requires)
  {
    match list
    case Nil => Nil
    case Cons(s, rest) => Cons(fn(s), fmapPartial(rest, fn))
  }

  function method of<T>(t: T, ghost pred: T -> bool): IList<T>
  requires pred(t)
  ensures IListForall(of(t, pred), pred)
  {
    IList.Cons(t, IList.Nil)
  }
}