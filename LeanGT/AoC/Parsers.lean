namespace String
  def tail (s : String) := String.mk s.toList.tail
end String

inductive Result (T : Type) : Type where
 | fail
 | finish (p : T)
 | more (p : T)


-- parse strings of the form `1,2,3)`

structure PairState : Type where
  x: Int
  acc: Array Int
deriving Repr, BEq

namespace PairState
  def consume (p : PairState) (c : Char) : Result PairState :=
    if c == ')' then
      let res := PairState.mk 0 (p.acc.push p.x)
      .finish res
    else if c == ',' then
      let res := PairState.mk 0 (p.acc.push p.x)
      .more res
    else if '0' <= c && c <= '9' then
      let x' := 10*p.x + (c.val - '0'.val).toNat
      let res := .mk x' p.acc
      .more res
    else
      .fail
end PairState

def matchPair_ (p : PairState) (s : String.Iterator) : Option PairState :=
  if s.atEnd then
    p
  else
    let p' := p.consume s.curr
    match p' with
    | Result.fail => none
    | Result.finish p'' => .some p''
    | Result.more p'' => matchPair_ p'' s.next

def matchPair := matchPair_ (.mk 0 #[])

#eval matchPair "1,0)".mkIterator

structure MulStruct: Type where
  n1: Int
  n2: Int
deriving Inhabited, Repr, BEq

def mulOfPair (x : PairState) : MulStruct :=
  if x.acc.size == 2 then
    .mk (x.acc.get! 0) (x.acc.get! 1)
  else
    .mk 0 0

-- Mul

structure MulState : Type where
  head: String
  acc: Array MulStruct
deriving Repr, BEq

namespace MulState
  def consume (p : MulState)  (c : Char) (s : String.Iterator): MulState :=
    if p.head.isEmpty then
      let lookahead := matchPair s
      match lookahead with
      | none => .mk "mul(" p.acc
      | some p' => .mk "mul(" (p.acc.push (mulOfPair p'))
    else if c == p.head.mkIterator.curr then
      .mk p.head.tail p.acc
    else
      .mk "mul(" p.acc
end MulState

def matchMul_ (p : MulState) (s : String.Iterator) : MulState :=
  if s.atEnd then
    p
  else
    let p' := p.consume s.curr s
    matchMul_ p' s.next


def matchMul := matchMul_ (.mk "mul(" #[])
