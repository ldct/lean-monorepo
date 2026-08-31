import IsoGraph
import Mathlib.Combinatorics.SimpleGraph.Paths

namespace IsoGraphPlayground.Degree

/-! ## Paths and minimum degree -/

/-- Every nonempty finite simple graph contains a path whose length is exactly
its minimum degree. -/
theorem SimpleGraph.exists_isPath_length_eq_minDegree {V : Type*} [Fintype V]
    [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    ∃ (u v : V) (p : G.Walk u v), p.IsPath ∧ p.length = G.minDegree := by
  classical
  obtain ⟨u, v, p, hp, hmax⟩ :=
    SimpleGraph.Walk.exists_isPath_forall_isPath_length_le_length G
  have hneighbors : G.neighborFinset v ⊆ p.support.toFinset.erase v := by
    intro w hw
    have hadj : G.Adj v w := (G.mem_neighborFinset v w).mp hw
    have hwne : w ≠ v := fun h ↦ G.loopless.irrefl v (h ▸ hadj)
    have hwmem : w ∈ p.support := by
      by_contra hn
      have hext : (p.concat hadj).IsPath := hp.concat hn hadj
      have hlen := hmax _ _ (p.concat hadj) hext
      simp at hlen
    simp [hwmem, hwne]
  have hdegree : G.degree v ≤ p.length := by
    rw [← G.card_neighborFinset_eq_degree]
    calc
      (G.neighborFinset v).card ≤ (p.support.toFinset.erase v).card :=
        Finset.card_le_card hneighbors
      _ = p.length := by
        rw [Finset.card_erase_of_mem (by simpa using p.end_mem_support)]
        rw [List.toFinset_card_of_nodup hp.support_nodup, p.length_support]
        omega
  have hmin : G.minDegree ≤ p.length := (G.minDegree_le_degree v).trans hdegree
  refine ⟨_, _, p.take G.minDegree, hp.take _, ?_⟩
  rw [SimpleGraph.Walk.take_length, Nat.min_eq_left hmin]

lemma IsoGraph.minDeg_le_maxDeg
  (G : IsoGraph) : G.minDeg ≤ G.maxDeg := _root_.IsoGraph.minDeg_le_maxDeg G

/-! ## Average degree -/

/-- The average of the vertex degrees, as an exact rational number. -/
def CGraph.avgDeg (G : CGraph) : ℚ :=
  (∑ v, (G.toSimple.degree v : ℚ)) / FinEnum.card G.V

/-- The handshaking lemma gives the usual formula for the average degree. -/
theorem CGraph.avgDeg_eq_two_mul_E_div_V (G : CGraph) :
    CGraph.avgDeg G = 2 * G.E / FinEnum.card G.V := by
  have h : ∑ v, G.toSimple.degree v = 2 * G.E := by
    grind [CGraph.E, SimpleGraph.sum_degrees_eq_twice_card_edges]
  rw [CGraph.avgDeg]
  norm_cast
  rw [h]

lemma CGraph.minDeg_le_avgDeg (G : CGraph) : G.minDeg ≤ CGraph.avgDeg G := by
  have hsum : ∑ _ : G.V, (G.minDeg : ℚ) ≤ ∑ v, (G.toSimple.degree v : ℚ) := by
    apply Finset.sum_le_sum
    intro v _
    exact_mod_cast G.toSimple.minDegree_le_degree v
  rw [Finset.sum_const, Finset.card_univ, G.fintypeCard, nsmul_eq_mul] at hsum
  rw [CGraph.avgDeg]
  cases isEmpty_or_nonempty G.V with
  | inl hV =>
    let _ := hV
    simp [CGraph.minDeg, SimpleGraph.minDegree_of_subsingleton]
  | inr hV =>
    have hcard : (0 : ℚ) < FinEnum.card G.V := by
      exact_mod_cast FinEnum.card_pos
    apply (le_div_iff₀ hcard).2
    simpa [mul_comm] using hsum

/-! ## Edge density and pruning low-degree vertices -/

/-- The number of edges per vertex.  This is half the average degree. -/
def CGraph.edgeDensity (G : CGraph) : ℚ :=
  G.E / FinEnum.card G.V

/-- Delete one vertex, retaining the induced graph on all the other vertices. -/
def CGraph.deleteVertex (G : CGraph) (v : G.V) : CGraph :=
  G.restrict (fun w ↦ w ≠ v)

@[simp] lemma CGraph.deleteVertex_card (G : CGraph) (v : G.V) :
    FinEnum.card (CGraph.deleteVertex G v).V = FinEnum.card G.V - 1 := by
  rw [show FinEnum.card (CGraph.deleteVertex G v).V =
      Fintype.card {w : G.V // w ≠ v} from
    FinEnum.card_eq_fintypeCard.trans (Fintype.card_congr' rfl),
    Fintype.card_subtype_compl (fun w : G.V ↦ w = v), Fintype.card_subtype_eq,
    ← FinEnum.card_eq_fintypeCard (α := G.V)]

def CGraph.deleteVertex_inducedSubgraphOf (G : CGraph) (v : G.V) :
    (CGraph.deleteVertex G v).InducedSubgraphOf G where
  toFun := Subtype.val
  injective' := Subtype.val_injective
  map_adj' _ _ h := h
  adj_map' _ _ h := h

lemma CGraph.deleteVertex_E (G : CGraph) (v : G.V) :
    (CGraph.deleteVertex G v).E = G.E - G.toSimple.degree v := by
  let eV : (CGraph.deleteVertex G v).V ≃ {w : G.V // w ∈ ({v}ᶜ : Set G.V)} :=
    Equiv.subtypeEquivRight (by intro w; simp)
  let e : (CGraph.deleteVertex G v).toSimple ≃g G.toSimple.induce {v}ᶜ :=
    { toEquiv := eV
      map_rel_iff' := by intro x y; rfl }
  rw [CGraph.E, CGraph.E, e.card_edgeFinset_eq,
    SimpleGraph.card_edgeFinset_induce_compl_singleton,
    SimpleGraph.card_edgeFinset_deleteIncidenceSet]

lemma CGraph.two_le_card_of_E_pos (G : CGraph) (hE : 0 < G.E) :
    2 ≤ FinEnum.card G.V := by
  have hne : G.toSimple ≠ ⊥ := CGraph.toSimple_ne_bot_iff.mpr hE
  obtain ⟨a, b, hab⟩ := SimpleGraph.ne_bot_iff_exists_adj.mp hne
  have hneab : a ≠ b := by
    grind [G.toSimple.loopless.irrefl]
  have hp : ({a, b} : Finset G.V).card ≤ Finset.univ.card :=
    Finset.card_le_card (Finset.subset_univ _)
  rw [Finset.card_pair hneab, Finset.card_univ, G.fintypeCard] at hp
  exact hp

/-- Deleting a vertex whose degree is at most the current edge density cannot
decrease edge density. -/
lemma CGraph.edgeDensity_le_deleteVertex (G : CGraph) (v : G.V) (hE : 0 < G.E)
    (hdeg : (G.toSimple.degree v : ℚ) ≤ CGraph.edgeDensity G) :
    CGraph.edgeDensity G ≤ CGraph.edgeDensity (CGraph.deleteVertex G v) := by
  have hcard2 := CGraph.two_le_card_of_E_pos G hE
  have hcard : (0 : ℚ) < FinEnum.card G.V := by positivity
  have hcard' : (0 : ℚ) < FinEnum.card G.V - 1 := by
    have hcardq2 : (2 : ℚ) ≤ FinEnum.card G.V := by norm_cast
    linarith
  have hdegree : G.toSimple.degree v ≤ G.E := by
    simpa [CGraph.E] using G.toSimple.degree_le_card_edgeFinset v
  rw [CGraph.edgeDensity, CGraph.edgeDensity, CGraph.deleteVertex_E,
    CGraph.deleteVertex_card]
  rw [Nat.cast_sub hdegree, Nat.cast_sub (by omega : 1 ≤ FinEnum.card G.V)]
  norm_num
  apply (div_le_div_iff₀ hcard hcard').2
  rw [CGraph.edgeDensity] at hdeg
  rw [le_div_iff₀ hcard] at hdeg
  grind

/-- Every graph with an edge has an induced subgraph whose minimum degree is
strictly larger than its edge density, while its edge density is at least that
of the original graph.  This is Proposition 1.2.2's vertex-pruning argument. -/
theorem CGraph.exists_inducedSubgraph_edgeDensity_lt_minDeg (G : CGraph)
    (hE : 0 < G.E) :
    ∃ H : CGraph, Nonempty (H.InducedSubgraphOf G) ∧
      CGraph.edgeDensity G ≤ CGraph.edgeDensity H ∧
      CGraph.edgeDensity H < H.minDeg := by
  generalize hn : FinEnum.card G.V = n
  induction n using Nat.strong_induction_on generalizing G with
  | h n ih =>
    by_cases hgood : CGraph.edgeDensity G < (G.minDeg : ℚ)
    · exact ⟨G, ⟨CGraph.InducedSubgraphOf.refl G⟩, le_rfl, hgood⟩
    · have hcard2 := CGraph.two_le_card_of_E_pos G hE
      have hcardpos : 0 < FinEnum.card G.V := by omega
      obtain ⟨v₀⟩ := FinEnum.card_pos_iff.mp hcardpos
      obtain ⟨v, hv⟩ := G.exists_degree_eq_minDeg v₀
      have hdeg : (G.toSimple.degree v : ℚ) ≤ CGraph.edgeDensity G := by
        rw [hv]
        exact le_of_not_gt hgood
      let G' := CGraph.deleteVertex G v
      have hdens : CGraph.edgeDensity G ≤ CGraph.edgeDensity G' :=
        CGraph.edgeDensity_le_deleteVertex G v hE hdeg
      have hGdens : 0 < CGraph.edgeDensity G := by
        apply div_pos
        · exact_mod_cast hE
        · exact_mod_cast hcardpos
      have hE' : 0 < G'.E := by
        by_contra hnot
        have hz : G'.E = 0 := Nat.eq_zero_of_not_pos hnot
        have hdenszero : CGraph.edgeDensity G' = 0 := by
          simp [CGraph.edgeDensity, hz]
        linarith
      have hlt : FinEnum.card G'.V < n := by
        rw [CGraph.deleteVertex_card, hn]
        omega
      obtain ⟨H, hHG', hdens', hmin⟩ := ih _ hlt G' hE' rfl
      exact ⟨H,
        ⟨hHG'.some.trans (CGraph.deleteVertex_inducedSubgraphOf G v)⟩,
        hdens.trans hdens', hmin⟩



end IsoGraphPlayground.Degree
