import Radix.Eval.Stmt

/-! Total-correctness rules for normal statement execution. These rules construct
finite, fuel-free BigStep derivations; in particular, the while rule proves
termination from a decreasing natural-number measure. They do not classify
rejection or faults as successful execution. -/
namespace Radix

/-- Scalars have storage whenever there is an active call frame. -/
theorem PState.setVar_exists (σ : PState) (x : String) (v : Value)
    (h : σ.frames ≠ []) : ∃ σ', σ.setVar x v = some σ' := by
  unfold PState.setVar PState.updateCurrentFrame
  cases he : σ.frames with
  | nil => exact False.elim (h he)
  | cons fr rest => exact ⟨_, rfl⟩

@[simp] theorem PState.getVar_setVar_same {σ σ' : PState} {x : String} {v : Value}
    (h : σ.setVar x v = some σ') : σ'.getVar x = some v := by
  unfold PState.setVar PState.updateCurrentFrame at h
  cases he : σ.frames with
  | nil => simp [he] at h
  | cons fr rest =>
    simp [he] at h; cases h
    simp [PState.getVar, PState.currentFrame, Env.get?, Env.set]

theorem PState.getVar_setVar_other {σ σ' : PState} {x y : String} {v : Value}
    (h : σ.setVar x v = some σ') (hne : y ≠ x) :
    σ'.getVar y = σ.getVar y := by
  unfold PState.setVar PState.updateCurrentFrame at h
  cases he : σ.frames with
  | nil => simp [he] at h
  | cons fr rest =>
    simp [he] at h; cases h
    simp [PState.getVar, PState.currentFrame, Env.get?, Env.set, he,
      Std.HashMap.getElem?_insert, Ne.symm hne]

theorem PState.getVar_setVar {σ σ' : PState} {x y : String} {v : Value}
    (h : σ.setVar x v = some σ') :
    σ'.getVar y = if y = x then some v else σ.getVar y := by
  split
  · next heq => subst y; exact getVar_setVar_same h
  · next hne => exact getVar_setVar_other h hne

theorem PState.setVar_hasFrame {σ σ' : PState} {x : String} {v : Value}
    (h : σ.setVar x v = some σ') : σ'.frames ≠ [] := by
  unfold PState.setVar PState.updateCurrentFrame at h
  cases he : σ.frames with
  | nil => simp [he] at h
  | cons fr rest => simp [he] at h; cases h; simp

/-- Scalar writes preserve the shared heap and byte streams. -/
theorem PState.setVar_shared {σ σ' : PState} {x : String} {v : Value}
    (h : σ.setVar x v = some σ') :
    σ'.heap = σ.heap ∧ σ'.input = σ.input ∧ σ'.cursor = σ.cursor ∧
      σ'.output = σ.output := by
  unfold PState.setVar PState.updateCurrentFrame at h
  cases he : σ.frames with
  | nil => simp [he] at h
  | cons fr rest => simp [he] at h; cases h; exact ⟨rfl, rfl, rfl, rfl⟩

/-- Every state satisfying the precondition has a complete normal execution
whose final state satisfies the postcondition. -/
def TotalTriple (pre : PState → Prop) (s : Stmt) (post : PState → Prop) : Prop :=
  ∀ σ, pre σ → ∃ σ', BigStep σ s (.normal σ') ∧ post σ'

namespace TotalTriple

theorem consequence (h : TotalTriple pre s post)
    (hp : ∀ σ, pre' σ → pre σ) (hq : ∀ σ, post σ → post' σ) :
    TotalTriple pre' s post' := by
  intro σ hσ
  obtain ⟨σ', hs, hσ'⟩ := h σ (hp σ hσ)
  exact ⟨σ', hs, hq σ' hσ'⟩

theorem skip : TotalTriple pre .skip pre :=
  fun σ hσ => ⟨σ, .skip, hσ⟩

theorem seq (ha : TotalTriple pre a middle) (hb : TotalTriple middle b post) :
    TotalTriple pre (a ;; b) post := by
  intro σ hσ
  obtain ⟨σ', ha', hm⟩ := ha σ hσ
  obtain ⟨σ'', hb', hq⟩ := hb σ' hm
  exact ⟨σ'', .seqNormal ha' hb', hq⟩

theorem assign
    (h : ∀ σ, pre σ → ∃ v σ', e.eval σ = some v ∧
      σ.setVar x v = some σ' ∧ post σ') :
    TotalTriple pre (.assign x e) post := by
  intro σ hσ
  obtain ⟨v, σ', he, hs, hp⟩ := h σ hσ
  exact ⟨σ', .assign he hs, hp⟩

theorem decl
    (h : ∀ σ, pre σ → ∃ v σ', e.eval σ = some v ∧
      σ.setVar x v = some σ' ∧ post σ') :
    TotalTriple pre (.decl x ty e) post := by
  intro σ hσ
  obtain ⟨v, σ', he, hs, hp⟩ := h σ hσ
  exact ⟨σ', .decl he hs, hp⟩

theorem ite (hc : ∀ σ, pre σ → ∃ b, c.eval σ = some (.bool b))
    (ht : TotalTriple (fun σ => pre σ ∧ c.eval σ = some (.bool true)) t post)
    (hf : TotalTriple (fun σ => pre σ ∧ c.eval σ = some (.bool false)) f post) :
    TotalTriple pre (.ite c t f) post := by
  intro σ hp
  obtain ⟨b, he⟩ := hc σ hp
  cases b with
  | false =>
    obtain ⟨σ', hs, hq⟩ := hf σ ⟨hp, he⟩
    exact ⟨σ', .ifFalse he hs, hq⟩
  | true =>
    obtain ⟨σ', hs, hq⟩ := ht σ ⟨hp, he⟩
    exact ⟨σ', .ifTrue he hs, hq⟩

/-- An invariant, a defined boolean condition, and a strictly decreasing
measure suffice to construct a finite normal execution of a loop. -/
theorem whileLoop (inv : PState → Prop) (measure : PState → Nat)
    (hc : ∀ σ, inv σ → ∃ b, c.eval σ = some (.bool b))
    (hb : ∀ σ, inv σ → c.eval σ = some (.bool true) →
      ∃ σ', BigStep σ body (.normal σ') ∧ inv σ' ∧ measure σ' < measure σ) :
    TotalTriple inv (.while c body)
      (fun σ => inv σ ∧ c.eval σ = some (.bool false)) := by
  intro σ hσ
  suffices h : ∀ n σ, measure σ = n → inv σ →
      ∃ σ', BigStep σ (.while c body) (.normal σ') ∧
        inv σ' ∧ c.eval σ' = some (.bool false) from h (measure σ) σ rfl hσ
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro σ hn hi
    obtain ⟨b, he⟩ := hc σ hi
    cases b with
    | false => exact ⟨σ, .whileFalse he, hi, he⟩
    | true =>
      obtain ⟨σ', hs, hi', hlt⟩ := hb σ hi he
      obtain ⟨σ'', hw, hi'', he''⟩ := ih (measure σ') (by omega) σ' rfl hi'
      exact ⟨σ'', .whileTrue he hs hw, hi'', he''⟩

/-- Lift the execution of the AST's left-associated statement list. -/
theorem block (h : TotalTriple pre (stmts.foldl (init := Stmt.skip) (· ;; ·)) post) :
    TotalTriple pre (.block stmts) post := by
  intro σ hp
  obtain ⟨σ', hs, hq⟩ := h σ hp
  exact ⟨σ', .block hs, hq⟩

end TotalTriple

/-- A successful normal execution of a sequence must complete both components. -/
theorem BigStep.seq_normal_iff : BigStep σ (a ;; b) (.normal σ') ↔
    ∃ middle, BigStep σ a (.normal middle) ∧ BigStep middle b (.normal σ') := by
  constructor
  · intro h; cases h with
    | seqNormal ha hb => exact ⟨_, ha, hb⟩
  · rintro ⟨middle, ha, hb⟩; exact .seqNormal ha hb

/-- Shared parsing and printing can be composed around a proof relating the
computation states; the computation relation need only preserve what the
shared suffix observes. -/
theorem BigStep.replace_middle
    (h : BigStep σ (before ;; (reference ;; suffix)) (.normal σ'))
    (replace : ∀ parsed result,
      BigStep σ before (.normal parsed) →
      BigStep parsed reference (.normal result) →
      BigStep result suffix (.normal σ') →
      ∃ result', BigStep parsed optimized (.normal result') ∧
        BigStep result' suffix (.normal σ')) :
    BigStep σ (before ;; (optimized ;; suffix)) (.normal σ') := by
  obtain ⟨parsed, hp, hrest⟩ := BigStep.seq_normal_iff.mp h
  obtain ⟨result, hr, hs⟩ := BigStep.seq_normal_iff.mp hrest
  obtain ⟨result', ho, hs'⟩ := replace parsed result hp hr hs
  exact .seqNormal hp (.seqNormal ho hs')

/-- Extract the invariant and false exit condition from a complete normal run. -/
theorem BigStep.while_normal_invariant
    (h : BigStep σ (.while c body) (.normal σ'))
    (inv : PState → Prop) (hi : inv σ)
    (preserve : ∀ a b, inv a → c.eval a = some (.bool true) →
      BigStep a body (.normal b) → inv b) :
    inv σ' ∧ c.eval σ' = some (.bool false) := by
  generalize hs : Stmt.while c body = s at h
  generalize hr : StmtResult.normal σ' = r at h
  induction h generalizing c body σ' with
  | whileFalse hc =>
    cases hs; cases hr; exact ⟨hi, hc⟩
  | whileTrue hc hb hw ihb ihw =>
    cases hs
    exact ihw (preserve _ _ hi hc hb) preserve rfl hr
  | whileReturn hc hb ih => cases hs; cases hr
  | whileReject hc hb ih => cases hs; cases hr
  | _ => cases hs

/-- Replace a computation while preserving a chosen final observation. The
optimized program may retain different local variables and heap contents. -/
theorem BigStep.replace_middle_observation (observe : PState → α)
    (h : BigStep σ (before ;; (reference ;; suffix)) (.normal σ'))
    (replace : ∀ parsed result,
      BigStep σ before (.normal parsed) →
      BigStep parsed reference (.normal result) →
      BigStep result suffix (.normal σ') →
      ∃ result' final', BigStep parsed optimized (.normal result') ∧
        BigStep result' suffix (.normal final') ∧ observe final' = observe σ') :
    ∃ final', BigStep σ (before ;; (optimized ;; suffix)) (.normal final') ∧
      observe final' = observe σ' := by
  obtain ⟨parsed, hp, hrest⟩ := BigStep.seq_normal_iff.mp h
  obtain ⟨result, hr, hs⟩ := BigStep.seq_normal_iff.mp hrest
  obtain ⟨result', final', ho, hs', heq⟩ := replace parsed result hp hr hs
  exact ⟨final', .seqNormal hp (.seqNormal ho hs'), heq⟩

end Radix
