module

public import PottsContinuity.Thm3.Prop4.LowestHeight
public import PottsContinuity.Thm3.Prop4.TiltedLimit

/-!
# Actual top-connection events in the tilted strip

The source's lowest-height events use paths on the infinite original graph.
Their openness follows from finite open path witnesses, without a finite-window
or boundary-identification surrogate. Closing edges raises the lowest height.
-/

@[expose] public section

open MeasureTheory Topology

namespace PottsContinuity.Thm3.Prop4

/-- An actual open adjacency reads precisely its original strip edge. -/
theorem tiltedOpenGraph_adj_iff (n : ℕ) (t : ℝ) (ω : TiltedConfiguration n t)
    (u v : tiltedStripVertices n t) :
    (tiltedOpenGraph n t ω).Adj u v ↔
      ∃ h : (tiltedStripGraph n t).Adj u v, ω ⟨s(u,v), h⟩ = true := by
  simp only [tiltedOpenGraph, SimpleGraph.fromEdgeSet_adj, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨⟨h, hω⟩, _⟩
    exact ⟨h, hω⟩
  · rintro ⟨h, hω⟩
    exact ⟨⟨h, hω⟩, h.ne⟩

/-- The source's height sublevel is exactly the existence of a low top-connected vertex. -/
theorem lowestTopConnectedHeight_le_iff (n : ℕ) (hn : 1 ≤ n) (t : ℝ)
    (ω : TiltedConfiguration n t) (k : ℤ) (a : ℝ) :
    lowestTopConnectedHeight n hn t ω k ≤ a ↔
      ∃ l : ℤ, tiltedConnectedToTop n t ω (k,l) ∧ (l : ℝ)-t*k ≤ a := by
  constructor
  · exact fun h => ⟨_,lowestTopConnectedVertex_connected n hn t ω k,h⟩
  · rintro ⟨l,hl,hla⟩
    exact (sub_le_sub_right (by exact_mod_cast lowestTopConnectedVertex_le n hn t ω k l hl)
      (t*k)).trans hla

end PottsContinuity.Thm3.Prop4
