module

public import PottsContinuity.Thm3.RSW.FiniteDualRectangleLocality

@[expose] public section

namespace PottsContinuity.RSW
open PD.FK PD.FK.Medial PD.RCInfinite
noncomputable section

/-- A sampled dual rectangle crossing survives erasing all original edges
outside a vertex set, provided every sampled bond it reads lies in that set. -/
theorem finiteClosedDualHorizontalRectangle_erasure_iff
    (V : Finset LatticeVertex) (l r b t : ℤ) (W : Set (V : Set LatticeVertex))
    (hW : ∀ c : LatticeBond,
      (l ≤ (c.faceBase false).1 ∧ (c.faceBase false).1 ≤ r ∧
        b ≤ (c.faceBase false).2 ∧ (c.faceBase false).2 ≤ t) →
      (l ≤ (c.faceBase true).1 ∧ (c.faceBase true).1 ≤ r ∧
        b ≤ (c.faceBase true).2 ∧ (c.faceBase true).2 ≤ t) →
      ∀ e : (finiteLatticeGraph V).edgeSet, frozenEdgeEmbedding V e = latticeBondEdge c →
        ∀ v ∈ e.val, v ∈ W)
    (A : Configuration (finiteLatticeGraph V)) :
    A ∈ finiteClosedDualHorizontalRectangle V l r b t ↔
      inducedConfigurationErasure W A ∈ finiteClosedDualHorizontalRectangle V l r b t := by
  apply finiteClosedDualHorizontalRectangle_iff_of_bondStates
  intro c hf ht
  simp only [latticeConfigurationBondState,finiteSubgraphConfiguration,dite_true]
  congr 1
  apply propext
  constructor
  · intro hm
    obtain ⟨e,he,heq⟩ := Finset.mem_map.mp hm
    exact Finset.mem_map.mpr ⟨e,(mem_inducedConfigurationErasure W A e).mpr
      ⟨he,hW c hf ht e heq⟩,heq⟩
  · exact fun hm => (Finset.map_subset_map.mpr (inducedConfigurationErasure_subset W A)) hm

end
end PottsContinuity.RSW
