import Playground.Artin.Chapter_2_2_exercises

/-!
# A small cancellation simproc for `Artin.Group`

The six lemmas at the start of `Chapter_2_4` differ only in their
parenthesization.  This experiment uses one simproc to put products into a
left-associated form and to cancel inverse pairs at the head or tail of such a
product.
-/

namespace Artin

variable {G : Type*} [Artin.Group G]

private theorem inv_mul_cancel_head (a b : G) : a⁻¹ * (a * b) = b := by
  rw [← Artin.Group.mul_assoc, Artin.Group.inv_mul_cancel, Artin.Group.one_mul]

private theorem mul_inv_cancel_head (a b : G) : a * (a⁻¹ * b) = b := by
  rw [← Artin.Group.mul_assoc, Artin.Group.mul_inv_cancel, Artin.Group.one_mul]

private theorem mul_inv_cancel_tail (a b : G) : a * b * b⁻¹ = a := by
  rw [Artin.Group.mul_assoc, Artin.Group.mul_inv_cancel, Artin.Group.mul_one]

private theorem inv_mul_cancel_tail (a b : G) : a * b⁻¹ * b = a := by
  rw [Artin.Group.mul_assoc, Artin.Group.inv_mul_cancel, Artin.Group.mul_one]

private theorem mul_assoc_left (a b c : G) : a * (b * c) = a * b * c :=
  (Artin.Group.mul_assoc a b c).symm

open Lean Meta in
simproc_decl artinGroupCancel (_ * _) := fun e => do
  let (``HMul.hMul, #[_, _, _, _, lhs, rhs]) := e.getAppFnArgs
    | return .continue
  -- a⁻¹ * (a * b)  ==>  b
  if let (``Inv.inv, #[_, _, a₁]) := lhs.getAppFnArgs then
    if let (``HMul.hMul, #[_, _, _, _, a₂, b]) := rhs.getAppFnArgs then
      if a₁ == a₂ then
        let proof ← mkAppM ``inv_mul_cancel_head #[a₁, b]
        let some (_, _, result) := (← inferType proof).eq? | return .continue
        return .visit { expr := result, proof? := some proof }
  -- a * (a⁻¹ * b)  ==>  b
  if let (``HMul.hMul, #[_, _, _, _, invA, b]) := rhs.getAppFnArgs then
    if let (``Inv.inv, #[_, _, a₂]) := invA.getAppFnArgs then
      if lhs == a₂ then
        let proof ← mkAppM ``mul_inv_cancel_head #[lhs, b]
        let some (_, _, result) := (← inferType proof).eq? | return .continue
        return .visit { expr := result, proof? := some proof }
  -- (a * b) * b⁻¹  ==>  a
  if let (``HMul.hMul, #[_, _, _, _, a, b₁]) := lhs.getAppFnArgs then
    if let (``Inv.inv, #[_, _, b₂]) := rhs.getAppFnArgs then
      if b₁ == b₂ then
        let proof ← mkAppM ``mul_inv_cancel_tail #[a, b₁]
        let some (_, _, result) := (← inferType proof).eq? | return .continue
        return .visit { expr := result, proof? := some proof }
  -- (a * b⁻¹) * b  ==>  a
  if let (``HMul.hMul, #[_, _, _, _, a, invB]) := lhs.getAppFnArgs then
    if let (``Inv.inv, #[_, _, b₁]) := invB.getAppFnArgs then
      if b₁ == rhs then
        let proof ← mkAppM ``inv_mul_cancel_tail #[a, rhs]
        let some (_, _, result) := (← inferType proof).eq? | return .continue
        return .visit { expr := result, proof? := some proof }
  -- a * (b * c)  ==>  (a * b) * c
  if let (``HMul.hMul, #[_, _, _, _, b, c]) := rhs.getAppFnArgs then
    let proof ← mkAppM ``mul_assoc_left #[lhs, b, c]
    let some (_, _, result) := (← inferType proof).eq? | return .continue
    return .visit { expr := result, proof? := some proof }
  return .continue

/-!
The six target statements, each proved by the simproc alone.  Its four
cancellation proof rules are derived from the five fields of `Artin.Group`.
-/

example (a b : G) : a⁻¹ * (a * b) = b := by
  simp only [artinGroupCancel]

example (a b : G) : a * (a⁻¹ * b) = b := by
  simp only [artinGroupCancel]

example (a b : G) : a * b * b⁻¹ = a := by
  simp only [artinGroupCancel]

example (a b c : G) : a⁻¹ * (a * b * c) = b * c := by
  simp only [artinGroupCancel]

example (a b c : G) : a * (a⁻¹ * b * c) = b * c := by
  simp only [artinGroupCancel]

example (a b : G) : a * b⁻¹ * b = a := by
  simp only [artinGroupCancel]

example (a b c d : G) : a * (b * (c * d)) = a * b * c * d := by
  simp only [artinGroupCancel]

example (a b : G) :
    (b⁻¹ * (a * b) * b⁻¹ = b⁻¹ * (b * a) * b⁻¹) ↔
      b⁻¹ * a = a * b⁻¹ := by
  simp only [artinGroupCancel]

end Artin
