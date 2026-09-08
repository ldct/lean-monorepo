import Radix.Benchmarks.ABC177C
import Radix.Benchmarks.PairSum
import Radix.Proofs.Hoare

namespace Radix.Benchmarks.ABC177C

set_option maxRecDepth 10000 in
theorem optimizedLoop_shape : optimizedLoop = .while (.binop .lt (.var "j$7") (.var "n$0"))
  (.block [
    .assign "answer$5" (.binop .mod
      (.binop .add (.var "answer$5") (.binop .mul (.var "running$6")
        (.arrGet (.var "a$1") (.var "j$7")))) (.var "m$4")),
    .assign "running$6" (.binop .mod
      (.binop .add (.var "running$6") (.arrGet (.var "a$1") (.var "j$7"))) (.var "m$4")),
    .assign "j$7" (.binop .add (.var "j$7") (.lit (.uint64 1)))]) := by rfl

/-- The loop only changes its three scalar accumulators. -/
structure ScanContext (initial σ : PState) (n : UInt64) (address : Addr) : Prop where
  frame : σ.frames ≠ []
  sizeVar : σ.getVar "n$0" = some (.uint64 n)
  arrayVar : σ.getVar "a$1" = some (.addr address)
  modulus : σ.getVar "m$4" = some (.uint64 1000000007)
  heap : σ.heap = initial.heap
  input : σ.input = initial.input
  cursor : σ.cursor = initial.cursor
  output : σ.output = initial.output

theorem ScanContext.setVar (ctx : ScanContext initial σ n address)
    (hs : σ.setVar x v = some σ')
    (hx : x ≠ "n$0" ∧ x ≠ "a$1" ∧ x ≠ "m$4") :
    ScanContext initial σ' n address := by
  obtain ⟨hh, hi, hc, ho⟩ := PState.setVar_shared hs
  exact ⟨PState.setVar_hasFrame hs,
    (PState.getVar_setVar_other hs hx.1.symm).trans ctx.sizeVar,
    (PState.getVar_setVar_other hs hx.2.1.symm).trans ctx.arrayVar,
    (PState.getVar_setVar_other hs hx.2.2.symm).trans ctx.modulus,
    hh.trans ctx.heap, hi.trans ctx.input, hc.trans ctx.cursor, ho.trans ctx.output⟩

private theorem nat_uint64 (j : Nat) (hj : j ≤ 200000) : j.toUInt64.toNat = j := by
  exact UInt64.toNat_ofNat_of_lt (by change j < 18446744073709551616; omega)

private theorem next_uint64 (j : Nat) : j.toUInt64 + 1 = (j + 1).toUInt64 := by
  simp [Nat.toUInt64, UInt64.ofNat_add]

/-- Execute the running-sum loop on a validated suffix of the retained input
array. The conclusion includes termination and the exact mathematical answer,
without an interpreter fuel bound. -/
theorem optimizedLoop_total (xs : List UInt64)
    (initial σ : PState) (n answer running : UInt64) (address : Addr) (j : Nat)
    (ctx : ScanContext initial σ n address)
    (hn : n.toNat ≤ 200000) (hlen : j + xs.length = n.toNat)
    (hanswer : σ.getVar "answer$5" = some (.uint64 answer))
    (hrunning : σ.getVar "running$6" = some (.uint64 running))
    (hj : σ.getVar "j$7" = some (.uint64 j.toUInt64))
    (ha : answer.toNat < 1000000007) (hr : running.toNat < 1000000007)
    (hvalues : ∀ x ∈ xs, x.toNat ≤ 1000000000)
    (harray : ∀ k x, xs[k]? = some x →
      initial.heap.read address (j + k) = some (.uint64 x)) :
    ∃ final result : _, BigStep σ optimizedLoop (.normal final) ∧
      ScanContext initial final n address ∧
      final.getVar "answer$5" = some (.uint64 result) ∧
      result.toNat = Radix.ABC177C.scanMod 1000000007 running.toNat answer.toNat
        (xs.map UInt64.toNat) := by
  induction xs generalizing σ answer running j with
  | nil =>
    have hjn : j.toUInt64 = n := by
      apply UInt64.toNat_inj.mp
      rw [nat_uint64 j (by simp at hlen; omega)]
      simpa using hlen
    have hc : (Expr.binop .lt (.var "j$7") (.var "n$0")).eval σ = some (.bool false) := by
      simp [Expr.eval, hj, ctx.sizeVar, hjn]
    refine ⟨σ, answer, ?_, ctx, hanswer, ?_⟩
    · rw [optimizedLoop_shape]; exact .whileFalse hc
    · simp [Radix.ABC177C.scanMod, Nat.mod_eq_of_lt ha]
  | cons x xs ih =>
    have hx : x.toNat ≤ 1000000000 := hvalues x (by simp)
    have hread : σ.heap.read address j = some (.uint64 x) := by
      rw [ctx.heap]
      simpa using harray 0 x (by simp)
    have hlt : j.toUInt64 < n := by
      rw [UInt64.lt_iff_toNat_lt, nat_uint64 j (by simp at hlen; omega)]
      simp at hlen; omega
    have hc : (Expr.binop .lt (.var "j$7") (.var "n$0")).eval σ = some (.bool true) := by
      simp [Expr.eval, hj, ctx.sizeVar, hlt]
    let answer' := (answer + running * x) % (1000000007 : UInt64)
    let running' := (running + x) % (1000000007 : UInt64)
    obtain ⟨σ₁, hs₁⟩ := PState.setVar_exists σ "answer$5" (.uint64 answer') ctx.frame
    have ctx₁ := ctx.setVar hs₁ (by decide)
    obtain ⟨σ₂, hs₂⟩ := PState.setVar_exists σ₁ "running$6" (.uint64 running') ctx₁.frame
    have ctx₂ := ctx₁.setVar hs₂ (by decide)
    obtain ⟨σ₃, hs₃⟩ := PState.setVar_exists σ₂ "j$7" (.uint64 (j+1).toUInt64) ctx₂.frame
    have ctx₃ := ctx₂.setVar hs₃ (by decide)
    have hjbound : j ≤ 200000 := by simp at hlen; omega
    have he₁ : (Expr.binop .mod
        (.binop .add (.var "answer$5") (.binop .mul (.var "running$6")
          (.arrGet (.var "a$1") (.var "j$7")))) (.var "m$4")).eval σ = some (.uint64 answer') := by
      simp [Expr.eval, hanswer, hrunning, ctx.arrayVar, hj, ctx.modulus,
        nat_uint64 j hjbound, hread, answer']
    have he₂ : (Expr.binop .mod
        (.binop .add (.var "running$6") (.arrGet (.var "a$1") (.var "j$7")))
        (.var "m$4")).eval σ₁ = some (.uint64 running') := by
      simp [Expr.eval, PState.getVar_setVar hs₁, hrunning, ctx.arrayVar, hj,
        ctx.modulus, nat_uint64 j hjbound, ctx₁.heap, ← ctx.heap, hread, running']
    have he₃ : (Expr.binop .add (.var "j$7") (.lit (.uint64 1))).eval σ₂ =
        some (.uint64 (j + 1).toUInt64) := by
      simp only [Expr.eval, PState.getVar_setVar hs₂, PState.getVar_setVar hs₁]
      simp [hj, -Nat.toUInt64_eq]
    have hb : BigStep σ (.block [
        .assign "answer$5" (.binop .mod
          (.binop .add (.var "answer$5") (.binop .mul (.var "running$6")
            (.arrGet (.var "a$1") (.var "j$7")))) (.var "m$4")),
        .assign "running$6" (.binop .mod
          (.binop .add (.var "running$6") (.arrGet (.var "a$1") (.var "j$7"))) (.var "m$4")),
        .assign "j$7" (.binop .add (.var "j$7") (.lit (.uint64 1)))]) (.normal σ₃) :=
      .block (.seqNormal (.seqNormal (.seqNormal .skip (.assign he₁ hs₁))
        (.assign he₂ hs₂)) (.assign he₃ hs₃))
    have han : answer'.toNat = (answer.toNat + running.toNat * x.toNat) % 1000000007 :=
      Radix.ABC177C.uint64_multiply_add_mod answer running x ha hr hx
    have hrn : running'.toNat = (running.toNat + x.toNat) % 1000000007 :=
      Radix.ABC177C.uint64_running_mod running x hr hx
    obtain ⟨final, result, hw, ctxf, hresult, hspec⟩ := ih σ₃ answer' running' (j+1) ctx₃
      (by simp at hlen ⊢; omega)
      (by simp [PState.getVar_setVar hs₃, PState.getVar_setVar hs₂, PState.getVar_setVar hs₁])
      (by simp [PState.getVar_setVar hs₃, PState.getVar_setVar hs₂])
      (PState.getVar_setVar_same hs₃)
      (by rw [han]; exact Nat.mod_lt _ (by decide))
      (by rw [hrn]; exact Nat.mod_lt _ (by decide))
      (fun y hy => hvalues y (by simp [hy]))
      (by intro k y hy; simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using harray (k+1) y (by simpa using hy))
    refine ⟨final, result, ?_, ctxf, hresult, ?_⟩
    · rw [optimizedLoop_shape] at hw ⊢
      exact .whileTrue hc hb hw
    · simpa [List.map_cons, Radix.ABC177C.scanMod, han, hrn] using hspec

/-- Exact suffix following the common parser, validation, modulus and answer
initialization in the optimized submission. -/
def optimizedTail : Stmt := .block (optimizedStatements.drop 9)

theorem optimizedTail_shape : optimizedTail = .block [
    .decl "running$6" .uint64 (.lit (.uint64 0)),
    .decl "j$7" .uint64 (.lit (.uint64 0)), optimizedLoop,
    .writeU64 (.var "answer$5"), .writeText "\n"] := by rfl

theorem optimizedTail_total (xs : List UInt64) (σ : PState) (n : UInt64) (address : Addr)
    (hf : σ.frames ≠ [])
    (hnvar : σ.getVar "n$0" = some (.uint64 n))
    (havar : σ.getVar "a$1" = some (.addr address))
    (hmvar : σ.getVar "m$4" = some (.uint64 1000000007))
    (hanswer : σ.getVar "answer$5" = some (.uint64 0))
    (hn : n.toNat ≤ 200000) (hlen : xs.length = n.toNat)
    (hvalues : ∀ x ∈ xs, x.toNat ≤ 1000000000)
    (harray : ∀ k x, xs[k]? = some x → σ.heap.read address k = some (.uint64 x)) :
    ∃ final result, BigStep σ optimizedTail (.normal final) ∧
      result.toNat = Radix.ABC177C.pairs (xs.map UInt64.toNat) % 1000000007 ∧
      final.output = σ.output ++ ByteIO.writeU64 result ++ "\n".toUTF8 := by
  have ctx : ScanContext σ σ n address := ⟨hf, hnvar, havar, hmvar, rfl, rfl, rfl, rfl⟩
  obtain ⟨σ₁, hs₁⟩ := PState.setVar_exists σ "running$6" (.uint64 0) hf
  have ctx₁ := ctx.setVar hs₁ (by decide)
  obtain ⟨σ₂, hs₂⟩ := PState.setVar_exists σ₁ "j$7" (.uint64 0) ctx₁.frame
  have ctx₂ := ctx₁.setVar hs₂ (by decide)
  obtain ⟨σ₃, result, hw, ctx₃, hresult, hspec⟩ :=
    optimizedLoop_total xs σ σ₂ n 0 0 address 0 ctx₂ hn (by simpa using hlen)
      (by simpa [PState.getVar_setVar hs₂, PState.getVar_setVar hs₁] using hanswer)
      (by simp [PState.getVar_setVar hs₂, PState.getVar_setVar hs₁])
      (by simpa using PState.getVar_setVar_same hs₂)
      (by decide) (by decide) hvalues (by simpa using harray)
  let σ₄ := {σ₃ with output := σ₃.output ++ ByteIO.writeU64 result}
  let σ₅ := {σ₄ with output := σ₄.output ++ "\n".toUTF8}
  refine ⟨σ₅, result, ?_, ?_, ?_⟩
  · rw [optimizedTail_shape]
    exact .block (.seqNormal (.seqNormal (.seqNormal
      (.seqNormal (.seqNormal .skip (.decl rfl hs₁)) (.decl rfl hs₂)) hw)
      (.writeU64 (by simpa [Expr.eval] using hresult))) .writeText)
  · simpa [Radix.ABC177C.scanMod_correct] using hspec
  · simp [σ₅, σ₄, ctx₃.output]

end Radix.Benchmarks.ABC177C
