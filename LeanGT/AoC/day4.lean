def example_string := "MMMSXXMASM
MSAMXMSMSA
AMXSXMAAMM
MSAMASMSMX
XMASAMXAMM
XXAMMXXAMA
SMSMSASXSS
SAXAMASAAA
MAMMMXMMMM
MXMXAXMASX"

declare_syntax_cat compClause
syntax "for " term " in " term : compClause
syntax "if " term : compClause

syntax "[" term " | " compClause,* "]" : term

def List.map' (xs : List α) (f : α → β) : List β := List.map f xs

macro_rules
  | `([$t:term |]) => `([$t])
  | `([$t:term | for $x in $xs]) => `(List.map' $xs  (λ $x => $t))
  | `([$t:term | if $x]) => `(if $x then [$t] else [])
  | `([$t:term | $c, $cs,*]) => `(List.flatten [[$t | $cs,*] | $c])

structure Point : Type where
  x: Int
  y: Int
  deriving Repr, BEq

instance : Add Point where
  add := λ p q => { x := p.x + q.x, y := p.y + q.y }

def deltas : List Point := [
  {x:=1, y:=-1},
  {x:=1, y:=1},
  {x:=-1, y:=1},
  {x:=-1, y:=-1}
]

def List.prod (xs : List α) (ys : List β) : List (α × β) := [(x, y) | for x in xs, for y in ys]

def l1 := [[p, p + q, p + q + r, p + q + r + s] | for p in deltas, for q in deltas, for r in deltas, for s in deltas]

#check l1

#eval List.dedup [1, 2, 1]

#eval l1

#eval example_string
