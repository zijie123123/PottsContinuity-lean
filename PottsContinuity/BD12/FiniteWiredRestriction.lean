module

public import PottsContinuity.PD.RCInfinite.SubgraphComparison
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef

/-! Wired domain comparison for every increasing event on a finite induced
lattice graph, beyond the all-open-cylinder specialization of shared PD. -/

@[expose] public section

namespace PottsContinuity.BD12
open PD.FK PD.RCInfinite
noncomputable section

/-- The actual inner restriction of a larger wired law is dominated by the
smaller wired law on every increasing finite configuration event. -/
theorem finite_wired_induced_restriction_probability_le {S T : Finset LatticeVertex}
    (θ : Parameters) (hST : S ⊆ T)
    (A : Set (Configuration (finiteLatticeGraph S))) (hA : IsUpperSet A) :
    (measure (finiteLatticeGraph T) θ (BoundaryCondition.wired (frozenVertexBoundary T))
      {C | embeddedConfigurationRestriction (finiteLatticeGraph S) (finiteLatticeGraph T)
        (finiteLatticeVertexEmbedding hST) (finiteLatticeGraph_map_le hST) C ∈ A}).toReal ≤
      (measure (finiteLatticeGraph S) θ (BoundaryCondition.wired (frozenVertexBoundary S)) A).toReal := by
  apply embeddedConfigurationRestriction_preimage_measure_le_wired_of_closedInterior
    (finiteLatticeVertexEmbedding hST) (finiteLatticeGraph_map_le hST) θ
    (BoundaryCondition.wired (frozenVertexBoundary T)) (frozenVertexBoundary S) _ _ A hA
  · intro x hx y hxy
    have hxnot : x.val ∉ PD.vertexBoundary S := by simpa only [frozenVertexBoundary, Set.mem_ofPred_eq] using hx
    have hyS : y.val ∈ S := by
      by_contra hy
      exact hxnot ⟨x.property, y.val, hxy, hy⟩
    exact ⟨⟨y.val, hyS⟩, Subtype.ext rfl, hxy⟩
  · intro x hx
    have hxnot : x.val ∉ PD.vertexBoundary S := by simpa only [frozenVertexBoundary, Set.mem_ofPred_eq] using hx
    intro hout
    change x.val ∈ PD.vertexBoundary T at hout
    obtain ⟨_, y, hxy, hyT⟩ := hout
    have hyS : y ∈ S := by
      by_contra hy
      exact hxnot ⟨x.property, y, hxy, hy⟩
    exact hyT (hST hyS)

end
end PottsContinuity.BD12
