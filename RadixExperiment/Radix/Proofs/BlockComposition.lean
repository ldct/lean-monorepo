import Radix.Proofs.Hoare

namespace Radix

@[simp] theorem BigStep.skip_normal_iff : BigStep σ .skip (.normal σ') ↔ σ' = σ := by
  constructor
  · intro h; cases h; rfl
  · intro h; subst σ'; exact .skip

private theorem foldl_normal (ss : List Stmt) (start : Stmt) :
    BigStep σ (ss.foldl (· ;; ·) start) (.normal σ') ↔
      ∃ middle, BigStep σ start (.normal middle) ∧
        BigStep middle (ss.foldl (· ;; ·) .skip) (.normal σ') := by
  induction ss generalizing start σ σ' with
  | nil => simp
  | cons s ss ih =>
    constructor
    · intro h
      obtain ⟨after, hfirst, hrest⟩ := (ih (start ;; s)).mp h
      obtain ⟨middle, hs, hstep⟩ := BigStep.seq_normal_iff.mp hfirst
      exact ⟨middle, hs, (ih (.skip ;; s)).mpr ⟨after, .seqNormal .skip hstep, hrest⟩⟩
    · rintro ⟨middle, hs, h⟩
      obtain ⟨after, hfirst, hrest⟩ := (ih (.skip ;; s)).mp h
      obtain ⟨before, hskip, hstep⟩ := BigStep.seq_normal_iff.mp hfirst
      cases hskip
      exact (ih (start ;; s)).mpr ⟨after, .seqNormal hs hstep, hrest⟩

@[simp] theorem BigStep.block_normal_iff :
    BigStep σ (.block ss) (.normal σ') ↔
      BigStep σ (ss.foldl (· ;; ·) .skip) (.normal σ') := by
  constructor
  · intro h; cases h with | block hb => exact hb
  · exact BigStep.block

theorem BigStep.block_append_normal_iff :
    BigStep σ (.block (as ++ bs)) (.normal σ') ↔
      ∃ middle, BigStep σ (.block as) (.normal middle) ∧
        BigStep middle (.block bs) (.normal σ') := by
  simp only [block_normal_iff, List.foldl_append]
  exact foldl_normal bs (as.foldl (· ;; ·) .skip)

end Radix
