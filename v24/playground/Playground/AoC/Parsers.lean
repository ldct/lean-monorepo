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

inductive Token: Type where
  | mul (n1: Int) (n2: Int)
  | start
  | halt
  deriving Inhabited, Repr, BEq

def mulOfPair (x : PairState) : Token :=
  if x.acc.size == 2 then
    .mul (x.acc.get! 0) (x.acc.get! 1)
  else
    .mul 0 0

-- Mul

structure MulState : Type where
  mulHead: String
  startHead: String
  stopHead: String
  acc: Array Token
deriving Repr, BEq

namespace MulState
  def consume (p : MulState)  (c : Char) (it : String.Iterator): MulState :=
    let m := p.mulHead
    let s := p.startHead
    let t := p.stopHead

    let m' := if c == m.mkIterator.curr then m.tail else m
    let s' := if c == s.mkIterator.curr then s.tail else s
    let t' := if c == t.mkIterator.curr then t.tail else t

    -- dbgTrace [p.startHead, p.mulHead, p.stopHead, "<-", c.toString, "->", m', s'].toString fun _ =>

    if m'.isEmpty then
      let lookahead := matchPair it.next
      match lookahead with
      | none => .mk "mul(" "do()" "don't()" p.acc
      | some p' => .mk "mul(" "do()" "don't()" (p.acc.push (mulOfPair p'))
    else if s'.isEmpty then
      .mk "mul(" "do()" "don't()" (p.acc.push .start)
    else if t'.isEmpty then
      .mk "mul(" "do()" "don't()" (p.acc.push .halt)
    else
      .mk
        (if m == m' then "mul(" else m')
        (if s == s' then "do(" else s')
        (if t == t' then "don't(" else t')
        p.acc
end MulState

def matchMul_ (p : MulState) (s : String.Iterator) : MulState :=
  if s.atEnd then
    p
  else
    let p' := p.consume s.curr s
    matchMul_ p' s.next


def matchMul := matchMul_ (.mk "mul(" "do()" "don't()" #[])

#eval matchMul "don't()do()".mkIterator
