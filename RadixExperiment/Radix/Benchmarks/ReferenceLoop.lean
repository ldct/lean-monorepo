import Radix.Benchmarks.ABC177C
import Radix.Benchmarks.PairSum
import Radix.Proofs.Hoare

namespace Radix.Benchmarks.ABC177C

/-- Inner pair-enumeration loop, extracted from the actual reference source. -/
def referenceInner : Stmt :=
  match referenceLoop with
  | .while _ (.block ss) => ss[1]!
  | _ => .skip

theorem referenceInner_code : referenceInner =
    .while (.binop .lt (.var "i$7") (.var "j$6"))
      (.block [
        .assign "answer$5" (.binop .mod
          (.binop .add (.var "answer$5") (.binop .mul
            (.arrGet (.var "a$1") (.var "i$7"))
            (.arrGet (.var "a$1") (.var "j$6")))) (.var "m$4")),
        .assign "i$7" (.binop .add (.var "i$7") (.lit (.uint64 1)))]) := by rfl

/-- Scalar-only computation retains all shared state and all other locals. -/
structure Preserves (names : List String) (before after : PState) : Prop where
  vars : ∀ name, name ∉ names → after.getVar name = before.getVar name
  heap : after.heap = before.heap
  input : after.input = before.input
  cursor : after.cursor = before.cursor
  output : after.output = before.output

namespace Preserves

theorem refl : Preserves names σ σ := ⟨fun _ _ => rfl, rfl, rfl, rfl, rfl⟩
theorem trans (h : Preserves names a b) (k : Preserves names b c) : Preserves names a c :=
  ⟨fun n hn => (k.vars n hn).trans (h.vars n hn), k.heap.trans h.heap,
    k.input.trans h.input, k.cursor.trans h.cursor, k.output.trans h.output⟩
theorem of_set (hs : σ.setVar x v = some σ') (hx : x ∈ names) : Preserves names σ σ' := by
  obtain ⟨hh, hi, hc, ho⟩ := PState.setVar_shared hs
  refine ⟨?_, hh, hi, hc, ho⟩
  intro y hy
  apply PState.getVar_setVar_other hs
  intro he
  subst y
  exact hy hx
theorem weaken (h : Preserves small a b) (sub : ∀ x ∈ small, x ∈ large) : Preserves large a b :=
  ⟨fun n hn => h.vars n (fun hs => hn (sub n hs)), h.heap, h.input, h.cursor, h.output⟩
end Preserves

def innerBody : Stmt := match referenceInner with | .while _ b => b | _ => .skip

theorem inner_iteration (σ : PState) (a : Addr) (i j answer x y : UInt64)
    (hf : σ.frames ≠ [])
    (hi : σ.getVar "i$7" = some (.uint64 i))
    (hj : σ.getVar "j$6" = some (.uint64 j))
    (ha : σ.getVar "a$1" = some (.addr a))
    (hm : σ.getVar "m$4" = some (.uint64 1000000007))
    (hanswer : σ.getVar "answer$5" = some (.uint64 answer))
    (hx : σ.heap.read a j.toNat = some (.uint64 x))
    (hy : σ.heap.read a i.toNat = some (.uint64 y)) :
    ∃ σ', BigStep σ innerBody (.normal σ') ∧
      σ'.getVar "answer$5" = some (.uint64 ((answer + y*x) % 1000000007)) ∧
      σ'.getVar "i$7" = some (.uint64 (i+1)) ∧
      σ'.frames ≠ [] ∧ Preserves ["answer$5", "i$7"] σ σ' := by
  obtain ⟨σ₁, hs₁⟩ := σ.setVar_exists "answer$5" (.uint64 ((answer+y*x)%1000000007)) hf
  obtain ⟨σ₂, hs₂⟩ := σ₁.setVar_exists "i$7" (.uint64 (i+1)) (PState.setVar_hasFrame hs₁)
  have hi₁ : σ₁.getVar "i$7" = some (.uint64 i) :=
    (PState.getVar_setVar_other hs₁ (by decide)).trans hi
  refine ⟨σ₂, ?_, ?_, PState.getVar_setVar_same hs₂,
    PState.setVar_hasFrame hs₂, ?_⟩
  · apply BigStep.block
    apply BigStep.seqNormal
    · apply BigStep.seqNormal BigStep.skip
      apply BigStep.assign (σ' := σ₁) (v := .uint64 ((answer+y*x)%1000000007)) _ hs₁
      simp [Expr.eval, BinOp.evalLazy, hanswer, ha, hi, hj, hm, hx, hy, BinOp.eval]
    · apply BigStep.assign (v := .uint64 (i+1)) _ hs₂
      simp [Expr.eval, BinOp.evalLazy, hi₁, BinOp.eval]
  · exact (PState.getVar_setVar_other hs₂ (by decide)).trans (PState.getVar_setVar_same hs₁)
  · exact (Preserves.of_set hs₁ (by simp)).trans (Preserves.of_set hs₂ (by simp))

theorem inner_total (ys : List UInt64) (σ : PState) (a : Addr) (i j answer x : UInt64)
    (hf : σ.frames ≠ [])
    (hi : σ.getVar "i$7" = some (.uint64 i))
    (hj : σ.getVar "j$6" = some (.uint64 j))
    (ha : σ.getVar "a$1" = some (.addr a))
    (hm : σ.getVar "m$4" = some (.uint64 1000000007))
    (hanswer : σ.getVar "answer$5" = some (.uint64 answer))
    (hx : σ.heap.read a j.toNat = some (.uint64 x))
    (hys : ∀ k (hk : k < ys.length), σ.heap.read a (i.toNat+k) = some (.uint64 ys[k]))
    (hend : i.toNat + ys.length = j.toNat)
    (hjbound : j.toNat ≤ 200000)
    (habound : answer.toNat < 1000000007)
    (hxbound : x.toNat ≤ 1000000000)
    (hybound : ∀ y ∈ ys, y.toNat ≤ 1000000000) :
    ∃ σ' result, BigStep σ referenceInner (.normal σ') ∧
      σ'.getVar "answer$5" = some (.uint64 result) ∧
      result.toNat = Radix.ABC177C.columnMod 1000000007 x.toNat answer.toNat (ys.map UInt64.toNat) ∧
      result.toNat < 1000000007 ∧ σ'.frames ≠ [] ∧
      Preserves ["answer$5", "i$7"] σ σ' := by
  induction ys generalizing σ i answer with
  | nil =>
    refine ⟨σ, answer, ?_, hanswer, rfl, habound, hf, Preserves.refl⟩
    rw [referenceInner_code]
    apply BigStep.whileFalse
    have hnot : ¬ i < j := by simp only [UInt64.lt_iff_toNat_lt]; simp at hend; omega
    simp [Expr.eval, BinOp.evalLazy, hi, hj, BinOp.eval, hnot]
  | cons y ys ih =>
    have hij : i < j := by simp only [UInt64.lt_iff_toNat_lt]; simp at hend; omega
    have hhead : σ.heap.read a i.toNat = some (.uint64 y) := by
      simpa using hys 0 (by simp)
    obtain ⟨σ₁, hb, hans₁, hi₁, hf₁, hp₁⟩ := inner_iteration σ a i j answer x y hf hi hj ha hm hanswer hx hhead
    have hinc : (i+1).toNat = i.toNat+1 := by
      rw [UInt64.toNat_add]
      have hlim : i.toNat + (1 : UInt64).toNat < 2^64 := by
        change i.toNat + 1 < 2^64
        have := hij
        rw [UInt64.lt_iff_toNat_lt] at this
        omega
      rw [Nat.mod_eq_of_lt hlim]
      rfl
    have hansNat := Radix.ABC177C.uint64_multiply_add_mod answer y x
      habound (by have := hybound y (by simp); omega) hxbound
    have hansBound : (((answer+y*x)%1000000007 : UInt64)).toNat < 1000000007 := by
      rw [hansNat]
      exact Nat.mod_lt _ (by decide)
    obtain ⟨σ₂, result, hw, hresult, hresultNat, hresultBound, hf₂, hp₂⟩ :=
      ih σ₁ (i+1) ((answer+y*x)%1000000007) hf₁ hi₁
        ((hp₁.vars "j$6" (by simp)).trans hj)
        ((hp₁.vars "a$1" (by simp)).trans ha)
        ((hp₁.vars "m$4" (by simp)).trans hm) hans₁
        (by simpa [hp₁.heap] using hx)
        (by
          intro k hk
          rw [hp₁.heap, hinc]
          have h := hys (k+1) (by simp; omega)
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h)
        (by simp at hend; omega) hansBound
        (by intro z hz; exact hybound z (by simp [hz]))
    refine ⟨σ₂, result, ?_, hresult, ?_, hresultBound, hf₂, hp₁.trans hp₂⟩
    · rw [referenceInner_code] at *
      apply BigStep.whileTrue _ hb hw
      simp [Expr.eval, BinOp.evalLazy, hi, hj, BinOp.eval, hij]
    · simpa [List.map_cons, Radix.ABC177C.columnMod, hansNat] using hresultNat

theorem referenceLoop_code : referenceLoop =
    .while (.binop .lt (.var "j$6") (.var "n$0"))
      (.block [.decl "i$7" .uint64 (.lit (.uint64 0)), referenceInner,
        .assign "j$6" (.binop .add (.var "j$6") (.lit (.uint64 1)))]) := by rfl

theorem reference_total (xs pre : List UInt64) (σ : PState) (a : Addr) (j n answer : UInt64)
    (hf : σ.frames ≠ [])
    (hj : σ.getVar "j$6" = some (.uint64 j))
    (hn : σ.getVar "n$0" = some (.uint64 n))
    (ha : σ.getVar "a$1" = some (.addr a))
    (hm : σ.getVar "m$4" = some (.uint64 1000000007))
    (hanswer : σ.getVar "answer$5" = some (.uint64 answer))
    (hpre : ∀ k (hk : k < pre.length), σ.heap.read a k = some (.uint64 pre[k]))
    (hxs : ∀ k (hk : k < xs.length), σ.heap.read a (j.toNat+k) = some (.uint64 xs[k]))
    (hjlen : j.toNat = pre.length)
    (hend : j.toNat + xs.length = n.toNat)
    (hnbound : n.toNat ≤ 200000)
    (habound : answer.toNat < 1000000007)
    (hprebound : ∀ y ∈ pre, y.toNat ≤ 1000000000)
    (hxsbound : ∀ y ∈ xs, y.toNat ≤ 1000000000) :
    ∃ σ' result, BigStep σ referenceLoop (.normal σ') ∧
      σ'.getVar "answer$5" = some (.uint64 result) ∧
      result.toNat = Radix.ABC177C.referenceMod 1000000007 answer.toNat
        (pre.map UInt64.toNat) (xs.map UInt64.toNat) ∧
      result.toNat < 1000000007 ∧ σ'.frames ≠ [] ∧
      Preserves ["answer$5", "i$7", "j$6"] σ σ' := by
  induction xs generalizing pre σ j answer with
  | nil =>
    refine ⟨σ, answer, ?_, hanswer, rfl, habound, hf, Preserves.refl⟩
    rw [referenceLoop_code]
    apply BigStep.whileFalse
    have hnot : ¬ j < n := by simp only [UInt64.lt_iff_toNat_lt]; simp at hend; omega
    simp [Expr.eval, BinOp.evalLazy, hj, hn, BinOp.eval, hnot]
  | cons x xs ih =>
    have hjn : j < n := by simp only [UInt64.lt_iff_toNat_lt]; simp at hend; omega
    have hjbound : j.toNat ≤ 200000 := by
      have := hjn
      rw [UInt64.lt_iff_toNat_lt] at this
      omega
    have hx : σ.heap.read a j.toNat = some (.uint64 x) := by simpa using hxs 0 (by simp)
    obtain ⟨σ₁, hs₁⟩ := σ.setVar_exists "i$7" (.uint64 0) hf
    have hp₁ : Preserves ["answer$5", "i$7", "j$6"] σ σ₁ := Preserves.of_set hs₁ (by simp)
    have hkeep : ∀ name, name ≠ "i$7" → σ₁.getVar name = σ.getVar name :=
      fun _ h => PState.getVar_setVar_other hs₁ h
    obtain ⟨σ₂, col, hc, hcol, hcolNat, hcolBound, hf₂, hp₂⟩ :=
      inner_total pre σ₁ a 0 j answer x (PState.setVar_hasFrame hs₁)
        (PState.getVar_setVar_same hs₁)
        ((hkeep _ (by decide)).trans hj) ((hkeep _ (by decide)).trans ha)
        ((hkeep _ (by decide)).trans hm) ((hkeep _ (by decide)).trans hanswer)
        (by simpa [hp₁.heap] using hx)
        (by intro k hk; simpa [hp₁.heap] using hpre k hk)
        (by simpa using hjlen.symm) hjbound habound
        (hxsbound x (by simp)) hprebound
    have hj₂ : σ₂.getVar "j$6" = some (.uint64 j) :=
      (hp₂.vars _ (by simp)).trans ((hkeep _ (by decide)).trans hj)
    obtain ⟨σ₃, hs₃⟩ := σ₂.setVar_exists "j$6" (.uint64 (j+1)) hf₂
    have hp₃ : Preserves ["answer$5", "i$7", "j$6"] σ₂ σ₃ := Preserves.of_set hs₃ (by simp)
    have hp : Preserves ["answer$5", "i$7", "j$6"] σ σ₃ :=
      hp₁.trans ((hp₂.weaken (by
        intro z hz
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hz ⊢
        rcases hz with hz | hz
        · exact Or.inl hz
        · exact Or.inr (Or.inl hz))).trans hp₃)
    have hinc : (j+1).toNat = j.toNat+1 := by
      rw [UInt64.toNat_add]
      have hlim : j.toNat + (1 : UInt64).toNat < 2^64 := by change j.toNat + 1 < 2^64; omega
      rw [Nat.mod_eq_of_lt hlim]
      rfl
    obtain ⟨σ₄, result, hw, hresult, hresultNat, hresultBound, hf₄, hp₄⟩ :=
      ih (pre ++ [x]) σ₃ (j+1) col (PState.setVar_hasFrame hs₃)
        (PState.getVar_setVar_same hs₃)
        ((hp.vars _ (by simp)).trans hn)
        ((hp.vars _ (by simp)).trans ha)
        ((hp.vars _ (by simp)).trans hm)
        ((PState.getVar_setVar_other hs₃ (by decide)).trans hcol)
        (by
          intro k hk
          rw [hp.heap]
          by_cases hkp : k < pre.length
          · simpa [List.getElem_append_left hkp] using hpre k hkp
          · have hkEq : k = pre.length := by simp at hk; omega
            subst k
            simpa [List.getElem_append_right (Nat.le_refl _), ← hjlen] using hx)
        (by
          intro k hk
          rw [hp.heap, hinc]
          have h := hxs (k+1) (by simp; omega)
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h)
        (by simp [List.length_append, hinc, hjlen])
        (by simp at hend; omega) hcolBound
        (by intro z hz; simp only [List.mem_append, List.mem_singleton] at hz
            rcases hz with hz | hz
            · exact hprebound z hz
            · subst z; exact hxsbound x (by simp))
        (by intro z hz; exact hxsbound z (by simp [hz]))
    refine ⟨σ₄, result, ?_, hresult, ?_, hresultBound, hf₄, hp.trans hp₄⟩
    · rw [referenceLoop_code] at *
      apply BigStep.whileTrue _ _ hw
      · simp [Expr.eval, BinOp.evalLazy, hj, hn, BinOp.eval, hjn]
      · apply BigStep.block
        apply BigStep.seqNormal
        · apply BigStep.seqNormal
          · apply BigStep.seqNormal BigStep.skip
            exact BigStep.decl rfl hs₁
          · exact hc
        · apply BigStep.assign (v := .uint64 (j+1)) _ hs₃
          simp [Expr.eval, BinOp.evalLazy, hj₂, BinOp.eval]
    · simpa [List.map_cons, List.map_append, Radix.ABC177C.referenceMod, hcolNat] using hresultNat

def referenceTail : Stmt := .block (referenceStatements.drop 9)

theorem referenceTail_shape : referenceTail = .block [
    .decl "j$6" .uint64 (.lit (.uint64 0)), referenceLoop,
    .writeU64 (.var "answer$5"), .writeText "\n"] := by rfl

theorem referenceTail_total (xs : List UInt64) (σ : PState) (n : UInt64) (address : Addr)
    (hf : σ.frames ≠ [])
    (hnvar : σ.getVar "n$0" = some (.uint64 n))
    (havar : σ.getVar "a$1" = some (.addr address))
    (hmvar : σ.getVar "m$4" = some (.uint64 1000000007))
    (hanswer : σ.getVar "answer$5" = some (.uint64 0))
    (hn : n.toNat ≤ 200000) (hlen : xs.length = n.toNat)
    (hvalues : ∀ x ∈ xs, x.toNat ≤ 1000000000)
    (harray : ∀ k (hk : k < xs.length), σ.heap.read address k = some (.uint64 xs[k])) :
    ∃ final result, BigStep σ referenceTail (.normal final) ∧
      result.toNat = Radix.ABC177C.pairs (xs.map UInt64.toNat) % 1000000007 ∧
      final.output = σ.output ++ ByteIO.writeU64 result ++ "\n".toUTF8 := by
  obtain ⟨σ₁, hs₁⟩ := σ.setVar_exists "j$6" (.uint64 0) hf
  have hp₁ : Preserves ["j$6"] σ σ₁ := Preserves.of_set hs₁ (by simp)
  obtain ⟨σ₂, result, hw, hresult, hspec, _, _, hp₂⟩ :=
    reference_total xs [] σ₁ address 0 n 0 (PState.setVar_hasFrame hs₁)
      (PState.getVar_setVar_same hs₁)
      ((hp₁.vars _ (by simp)).trans hnvar)
      ((hp₁.vars _ (by simp)).trans havar)
      ((hp₁.vars _ (by simp)).trans hmvar)
      ((hp₁.vars _ (by simp)).trans hanswer)
      (by intro k hk; simp at hk)
      (by intro k hk; simpa [hp₁.heap] using harray k hk)
      rfl (by simpa using hlen) hn (by decide) (by simp) hvalues
  let σ₃ := {σ₂ with output := σ₂.output ++ ByteIO.writeU64 result}
  let σ₄ := {σ₃ with output := σ₃.output ++ "\n".toUTF8}
  refine ⟨σ₄, result, ?_, ?_, ?_⟩
  · rw [referenceTail_shape]
    exact .block (.seqNormal (.seqNormal (.seqNormal
      (.seqNormal .skip (.decl rfl hs₁)) hw)
      (.writeU64 (by simpa [Expr.eval] using hresult))) .writeText)
  · simpa [Radix.ABC177C.referenceMod_correct _ 1000000007 (by decide)] using hspec
  · simp [σ₄, σ₃, hp₂.output, hp₁.output]

end Radix.Benchmarks.ABC177C
