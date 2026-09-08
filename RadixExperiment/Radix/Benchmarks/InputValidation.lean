import Radix.Benchmarks.ABC177C
import Radix.Benchmarks.InputFacts

namespace Radix.Benchmarks.ABC177C
open Radix.ABC177C

def InputInvariant (n : UInt64) (a : Addr) (σ : PState) : Prop :=
  σ.getVar "n$0" = some (.uint64 n) ∧ σ.getVar "a$1" = some (.addr a) ∧
  σ.frames ≠ [] ∧ ∃ values, σ.heap.lookup a = some values ∧
    values.size = n.toNat ∧ BoundedValues values

theorem InputInvariant.setVar (h : InputInvariant n a σ)
    (hs : σ.setVar x v = some σ') (hn : x ≠ "n$0") (ha : x ≠ "a$1") :
    InputInvariant n a σ' := by
  obtain ⟨hnv, hav, hf, values, hl, hsize, hb⟩ := h
  exact ⟨by simpa [PState.getVar_setVar hs, Ne.symm hn] using hnv,
    by simpa [PState.getVar_setVar hs, Ne.symm ha] using hav,
    PState.setVar_hasFrame hs, values, by simpa [(PState.setVar_shared hs).1] using hl,
    hsize, hb⟩

theorem InputInvariant.cursor (h : InputInvariant n a σ) (cursor : Nat) :
    InputInvariant n a {σ with cursor} := h

def inputBody : Stmt := .block [
  .decl "x$3" .uint64 (.lit (.uint64 0)),
  .readU64 "x$3",
  .ite (.binop .gt (.var "x$3") (.lit (.uint64 1000000000))) (.block [.reject]) .skip,
  .arrSet (.var "a$1") (.var "k$2") (.var "x$3"),
  .assign "k$2" (.binop .add (.var "k$2") (.lit (.uint64 1)))]

theorem inputBody_preserves (hi : InputInvariant n a σ)
    (h : BigStep σ inputBody (.normal σ')) : InputInvariant n a σ' := by
  cases h with
  | block h =>
    simp only [List.foldl] at h
    obtain ⟨s4, h, hassign⟩ := BigStep.seq_normal_iff.mp h
    obtain ⟨s3, h, hwrite⟩ := BigStep.seq_normal_iff.mp h
    obtain ⟨s2, h, hguard⟩ := BigStep.seq_normal_iff.mp h
    obtain ⟨s1, h, hread⟩ := BigStep.seq_normal_iff.mp h
    obtain ⟨s0, hskip, hdecl⟩ := BigStep.seq_normal_iff.mp h
    cases hskip
    cases hdecl with
    | decl he hs =>
      have hi1 := hi.setVar hs (by decide) (by decide)
      cases hread with
      | readU64 hr hsread =>
        rename_i readN cursor
        have hi2 := (hi1.cursor _).setVar hsread (by decide) (by decide)
        have hx := PState.getVar_setVar_same hsread
        obtain ⟨hc, rfl⟩ := validation_false hguard
        simp [Expr.eval, hx, BinOp.evalLazy, UInt64.lt_iff_toNat_lt] at hc
        cases hwrite with
        | arrSet harr hidx hval hw =>
          simp only [Expr.eval, hi2.2.1, Option.some.injEq, Value.addr.injEq] at harr
          cases harr
          simp only [Expr.eval, hx, Option.some.injEq] at hval
          cases hval
          cases hassign with
          | assign he hs =>
            refine InputInvariant.setVar ?_ hs (by decide) (by decide)
            obtain ⟨hnv, hav, hf, values, hl, hsize, hbounded⟩ := hi2
            refine ⟨hnv, hav, hf, ?_⟩
            unfold Heap.write at hw
            simp only [hl, bind, Option.bind] at hw
            split at hw
            · rename_i hidxBound
              simp only [Option.some.injEq] at hw
              cases hw
              refine ⟨values.set _ (.uint64 readN), by simp [Heap.lookup], by simpa using hsize,
                bounded_set hbounded _ hidxBound _ ?_⟩
              exact hc
            · simp at hw


/-- The facts established by the actual shared input-validation code. -/
def Validated (σ : PState) : Prop :=
  ∃ n a, 2 ≤ n.toNat ∧ n.toNat ≤ 200000 ∧ InputInvariant n a σ ∧
    σ.getVar "m$4" = some (.uint64 1000000007) ∧
    σ.getVar "answer$5" = some (.uint64 0)

theorem inputPrefix_validates (h : BigStep σ inputPrefix (.normal σ')) : Validated σ' := by
  cases h with
  | block h =>
    change BigStep σ
      (((((((((.skip ;; .decl "n$0" .uint64 (.lit (.uint64 0))) ;;
      .readU64 "n$0") ;;
      .ite (.binop .or (.binop .lt (.var "n$0") (.lit (.uint64 2)))
        (.binop .gt (.var "n$0") (.lit (.uint64 200000)))) (.block [.reject]) .skip) ;;
      .alloc "a$1" .uint64 (.var "n$0")) ;;
      .decl "k$2" .uint64 (.lit (.uint64 0))) ;;
      .while (.binop .lt (.var "k$2") (.var "n$0")) inputBody) ;;
      .expectEof) ;; .decl "m$4" .uint64 (.lit (.uint64 1000000007))) ;;
      .decl "answer$5" .uint64 (.lit (.uint64 0))) (.normal σ') at h
    obtain ⟨s8, h, hans⟩ := BigStep.seq_normal_iff.mp h
    obtain ⟨s7, h, hm⟩ := BigStep.seq_normal_iff.mp h
    obtain ⟨s6, h, heof⟩ := BigStep.seq_normal_iff.mp h
    obtain ⟨s5, h, hloop⟩ := BigStep.seq_normal_iff.mp h
    obtain ⟨s4, h, hk⟩ := BigStep.seq_normal_iff.mp h
    obtain ⟨s3, h, halloc⟩ := BigStep.seq_normal_iff.mp h
    obtain ⟨s2, h, hguard⟩ := BigStep.seq_normal_iff.mp h
    obtain ⟨s1, h, hread⟩ := BigStep.seq_normal_iff.mp h
    cases hread with
    | readU64 hr hsread =>
      rename_i n cursor
      have hn := PState.getVar_setVar_same hsread
      obtain ⟨hc, rfl⟩ := validation_false hguard
      have bounds : 2 ≤ n.toNat ∧ n.toNat ≤ 200000 := by
        simp [Expr.eval, hn, BinOp.evalLazy, UInt64.lt_iff_toNat_lt] at hc
        split at hc <;> simp_all
      cases halloc with
      | @alloc a heap _ _ _ _ _ sz he ha hsalloc =>
        simp only [Expr.eval, hn, Option.some.injEq, Value.uint64.injEq] at he
        cases he
        have hi4 : InputInvariant n a s4 := by
          refine ⟨?_, PState.getVar_setVar_same hsalloc, PState.setVar_hasFrame hsalloc, ?_⟩
          · simpa [PState.getVar_setVar hsalloc] using hn
          · simp only [Heap.alloc, Prod.mk.injEq] at ha
            obtain ⟨rfl, rfl⟩ := ha
            refine ⟨Array.replicate n.toNat (.uint64 0), ?_, by simp, bounded_zeros _⟩
            rw [(PState.setVar_shared hsalloc).1]
            simp [Heap.lookup]
        cases hk with
        | decl he hsk =>
          have hi5 := hi4.setVar hsk (by decide) (by decide)
          have hi6 := (BigStep.while_normal_invariant hloop (InputInvariant n a) hi5
            (fun _ _ hi _ hb => inputBody_preserves hi hb)).1
          cases heof with
          | expectEof he =>
            have hi7 := hi6.cursor s6.input.size
            cases hm with
            | decl hem hsm =>
              simp only [Expr.eval, Option.some.injEq] at hem
              cases hem
              have hi8 := hi7.setVar hsm (by decide) (by decide)
              have hmv := PState.getVar_setVar_same hsm
              cases hans with
              | decl hea hsa =>
                simp only [Expr.eval, Option.some.injEq] at hea
                cases hea
                exact ⟨n, _, bounds.1, bounds.2,
                  hi8.setVar hsa (by decide) (by decide),
                  by simpa [PState.getVar_setVar hsa] using hmv,
                  PState.getVar_setVar_same hsa⟩


private def unsignedValue : Value → UInt64
  | .uint64 n => n
  | _ => 0

theorem InputInvariant.toList (h : InputInvariant n a σ) :
    ∃ xs : List UInt64, xs.length = n.toNat ∧
      (∀ x ∈ xs, x.toNat ≤ 1000000000) ∧
      (∀ k (hk : k < xs.length), σ.heap.read a k = some (.uint64 xs[k])) := by
  obtain ⟨_, _, _, values, hl, hsize, hb⟩ := h
  let xs := values.toList.map unsignedValue
  have hlen : xs.length = values.size := by simp [xs]
  have cell (k : Nat) (hk : k < xs.length) :
      values[k]'(by omega) = .uint64 xs[k] := by
    obtain ⟨v, hv, _⟩ := hb k (by omega)
    simp only [xs, List.getElem_map, Array.getElem_toList]
    change values[k] = .uint64 (unsignedValue values[k])
    simp only [hv, unsignedValue]
  refine ⟨xs, hlen.trans hsize, ?_, ?_⟩
  · intro x hx
    obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hx
    obtain ⟨v, hv, hvb⟩ := hb k (by omega)
    have heq := cell k hk
    rw [hv] at heq
    cases Value.uint64.inj heq
    exact hvb
  · intro k hk
    simp [Heap.read, hl, Array.getElem?_eq_getElem (show k < values.size by omega), cell k hk]

end Radix.Benchmarks.ABC177C
