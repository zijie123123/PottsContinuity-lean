module

public import PottsContinuity.PlanarMixed.CanonicalCutBonds

/-! The union of the two closed exterior reveals is exactly the complement
of the induced band with all minimally prewired arc bonds removed.
-/

@[expose] public section

namespace PottsContinuity.PlanarMixed
open PD.FK
noncomputable section
variable {V : Type*} [Finite V]

omit [Finite V] in
/-- Adjacency after deleting a specified original bond carrier. -/
theorem edgeRestriction_adj_exists_not_mem (G : SimpleGraph V) (R : Configuration G) (u v : V) :
    (edgeRestriction G R).Adj u v ↔
      ∃ h : G.Adj u v, (⟨s(u,v), G.mem_edgeSet.mpr h⟩ : G.edgeSet) ∉ R := by
  rw [edgeRestriction, SimpleGraph.deleteEdges_adj]
  constructor
  · rintro ⟨hG,hn⟩
    exact ⟨hG, fun he => hn ((coe_mem_openEdges_iff G R _).mpr he)⟩
  · rintro ⟨hG,hn⟩
    exact ⟨hG, fun he => hn ((coe_mem_openEdges_iff G R _).mp he)⟩

/-- Deleting both one-sided closed reveals leaves exactly the actual active
band graph, retaining all original vertices as isolated outside the band. -/
theorem outerCutReveal_active_graph (G : SimpleGraph V) (r : V → ℤ)
    (hstep : RankedBandEdges G r) :
    edgeRestriction G (outerCutReveal G r) =
      (edgeRestriction (rankedBandGraph G r) (bandArcBonds G r)).map (rankedBandEmbedding r) := by
  apply SimpleGraph.ext
  funext x y
  apply propext
  constructor
  · intro hxy
    obtain ⟨hG,hn⟩ := (edgeRestriction_adj_exists_not_mem G _ x y).mp hxy
    have hout : ¬ ((r x ≤ 1 ∧ r y ≤ 1) ∨ (3 ≤ r x ∧ 3 ≤ r y)) :=
      fun h => hn ((mem_outerCutReveal_pair G r x y hG).mpr h)
    have hb : (1 ≤ r x ∧ r x ≤ 3) ∧ (1 ≤ r y ∧ r y ≤ 3) := by
      rcases hstep x y hG with hleft | hband | hright
      · exact (hout (Or.inl hleft)).elim
      · exact hband
      · exact (hout (Or.inr hright)).elim
    let vx : rankedBandVertices r := ⟨x,hb.1⟩
    let vy : rankedBandVertices r := ⟨y,hb.2⟩
    apply (SimpleGraph.map_adj _ _ _ _).mpr
    refine ⟨vx,vy,?_,rfl,rfl⟩
    apply (edgeRestriction_adj_exists_not_mem (rankedBandGraph G r) _ vx vy).mpr
    refine ⟨hG,?_⟩
    intro he
    rcases (mem_bandArcBonds_pair G r vx vy hG).mp he with hfirst | hsecond
    · change r x = 1 ∧ r y = 1 at hfirst
      exact hout (Or.inl ⟨by omega, by omega⟩)
    · change r x = 3 ∧ r y = 3 at hsecond
      exact hout (Or.inr ⟨by omega, by omega⟩)
  · intro hxy
    obtain ⟨vx,vy,hactive,rfl,rfl⟩ := (SimpleGraph.map_adj _ _ _ _).mp hxy
    obtain ⟨hG,hn⟩ := (edgeRestriction_adj_exists_not_mem (rankedBandGraph G r) _ vx vy).mp hactive
    apply (edgeRestriction_adj_exists_not_mem G _ vx.val vy.val).mpr
    refine ⟨hG,?_⟩
    have hx : 1 ≤ r vx.val ∧ r vx.val ≤ 3 := vx.property
    have hy : 1 ≤ r vy.val ∧ r vy.val ≤ 3 := vy.property
    intro he
    rcases (mem_outerCutReveal_pair G r vx.val vy.val hG).mp he with hleft | hright
    · apply hn
      apply (mem_bandArcBonds_pair G r vx vy hG).mpr
      exact Or.inl ⟨by omega, by omega⟩
    · apply hn
      apply (mem_bandArcBonds_pair G r vx vy hG).mpr
      exact Or.inr ⟨by omega, by omega⟩

/-- Exact revealed-bond carrier identity, not just an inclusion. -/
theorem outerCutReveal_eq_active_complement (G : SimpleGraph V) (r : V → ℤ)
    (hstep : RankedBandEdges G r) :
    outerCutReveal G r = subgraphRemovedEdges
      ((edgeRestriction (rankedBandGraph G r) (bandArcBonds G r)).map (rankedBandEmbedding r)) G := by
  classical
  symm
  apply Finset.ext
  intro e
  rw [mem_subgraphRemovedEdges, ← outerCutReveal_active_graph G r hstep, edgeRestriction_edgeSet]
  simp only [Set.mem_sdiff, e.property, true_and, not_not, coe_mem_openEdges_iff]

end
end PottsContinuity.PlanarMixed
