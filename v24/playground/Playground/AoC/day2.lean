import Std
import Playground.AoC.day2_data

open Day2Data

#eval lst2.length

def l1 := [1]
def l2 := [2]

example (h : l1 = l2) : False := by
  unfold l1 at h
  have h' : l1 ≠ l2 := by decide
  exact h' h


def differences_ (prev : Int) (lst : List Int) : List Int :=
  match lst with
    | [] => []
    | x :: xs => .cons (x - prev) (differences_ x xs)

def differences (lst : List Int) : List Int := (differences_ 0 lst).tail

def pos (x : Int) : Bool := x > 0
def neg (x : Int) : Bool := x < 0

def inRange (x : Int) : Bool :=
  let d := Int.natAbs x
  1 <= d ∧ d <= 3

def isSafe (lst : List Int) : Bool :=
  let d := differences lst
  ((d.all pos) ∨ (d.all neg)) ∧ (d.all inRange)

#eval (lst2.filter isSafe).length

def dropNth_ (idx : Int) (lst1 : List Int) (lst2 : List Int) : List Int :=
  match lst1 with
  | [] => lst2
  | x :: xs =>
    dropNth_ (idx - 1) xs (if idx == 0 then lst2 else (.cons x lst2))

def dropNth' (idx : Int) (lst : List Int) : List Int :=
  (dropNth_ idx lst []).reverse

def dropNth (idx : Nat) (lst : List Int) : List Int :=
  dropNth' idx lst

example : dropNth 3 [0, 1, 2, 3, 4, 5] = [0, 1, 2, 4, 5] := by decide

def dropAll (lst : List Int) : List (List Int) :=
  let idxs := (List.range (lst.length))
  idxs.map (fun x ↦ dropNth x lst)

example : dropAll [0, 1, 2] = [[1, 2], [0, 2], [0, 1]] := by decide

def newIsSafe (lst : List Int) : Bool :=
  (dropAll lst).any isSafe

example : newIsSafe [1,3,2,4,5] = true := by decide
example : newIsSafe [1,2,7,8,9] = false := by decide

#eval (lst2.filter newIsSafe).length
