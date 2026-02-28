import Batteries.Data.List.Basic
import Playground.AoC.day4

namespace Day4P2
open Day4
open Day4

instance : Neg Point where
  neg := λ p => { x := -p.x, y := -p.y }

def deltas : List Point := [
  {x:=-1, y:=-1}
]

def go3 (p : Point) := [-p, {x:=0, y:=0}, p]

def nw := go3 {x:=-1, y:=-1}
def ne := go3 {x:=-1, y:=1}
def sw := go3 {x:=1, y:=-1}
def se := go3 {x:=1, y:=1}

#eval sw


def offsets: List (List Point) := [
  sw.append se,
  nw.append ne,
  nw.append sw,
  ne.append se
]

#eval offsets

def lookup_ (p : Point') :=
  let y := arr.getD p.x "_"
  let z := y.toList.getD p.y '_'
  z

def lookup (p : List Point') := (p.map lookup_).asString

def idxsFrom (base : Point) :=
  (offsets.map fun y ↦ (y.map fun x ↦ (base + x).toPoint').reduceOption)

def wordsFrom (base : Point) :=
  (idxsFrom (base)).map lookup

def n := arr.length
#eval n

def starts := [Point.mk p q | for p in List.range n, for q in List.range n]

def countStartingFrom (base : Point) :=
  (wordsFrom base).count "MASMAS"

def p := Point.mk 1 2
#eval idxsFrom p
#eval wordsFrom p
#eval countStartingFrom p

-- #eval (starts.map countStartingFrom).sum  -- stack overflow on large input

end Day4P2
