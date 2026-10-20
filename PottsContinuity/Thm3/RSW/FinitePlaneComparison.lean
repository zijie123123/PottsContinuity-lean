module

public import PottsContinuity.Thm3.RSW.FiniteBoundary
public import PottsContinuity.Infinite.FiniteGraphComparison

@[expose] public section

namespace PottsContinuity.RSW
open MeasureTheory PD.FK PD.RCInfinite
noncomputable section
attribute [local instance] configurationMeasurableSpace

/-- Read exactly the sampled original lattice edges in a finite induced domain. -/
def finitePlaneBoolRestriction (V : Finset LatticeVertex) (ω : LatticeConfiguration) :
    (squareLattice.induce (V : Set LatticeVertex)).edgeSet → Bool :=
  fun e => ω (frozenEdgeEmbedding V e)

/-- Every increasing Boolean event under its finite free law is dominated by
its literal original-edge restriction in every genuine free infinite-volume limit. -/
theorem finite_free_event_le_infinite
    (θ : Parameters) (V : Finset LatticeVertex)
    (E : ((squareLattice.induce (V : Set LatticeVertex)).edgeSet → Bool) → Prop)
    (hE : IsUpperSet {ω | E ω}) (μ : Measure LatticeConfiguration)
    (hμ : IsRCInfiniteVolumeLimit θ.toP θ.toQ 0 μ) :
    finiteBoundaryEventProbability V θ (frozenBoundaryCondition V 0) E ≤
      μ.real {ω | E (finitePlaneBoolRestriction V ω)} := by
  classical
  let G := squareLattice.induce (V : Set LatticeVertex)
  let f : (V : Set LatticeVertex) ↪ LatticeVertex := ⟨Subtype.val,Subtype.val_injective⟩
  have hG : G.map f ≤ squareLattice := by
    intro x y hxy
    obtain ⟨u,v,huv,rfl,rfl⟩ := (SimpleGraph.map_adj f G x y).mp hxy
    exact huv
  have hθ : Infinite.pdParameters θ.toP θ.toQ (edgeParameter_pos θ)
      (edgeParameter_lt_one θ) θ.property = θ := by
    cases θ
    rfl
  have hcmp := Infinite.finite_graph_free_le_infinite_local θ.toP θ.toQ
    (edgeParameter_pos θ) (edgeParameter_lt_one θ) θ.property G f hG
    (finiteBoolEvent V E) (finiteBoolEvent_isUpperSet V E hE) μ hμ
  rw [hθ] at hcmp
  have hevent : Infinite.latticeGraphEvent G f hG (finiteBoolEvent V E) =
      {ω | E (finitePlaneBoolRestriction V ω)} := by
    ext ω
    change E ((boolConfigurationEquiv G).symm
      (Infinite.latticeGraphRestriction G f hG ω)) ↔ E (finitePlaneBoolRestriction V ω)
    have hrestr : (boolConfigurationEquiv G).symm
        (Infinite.latticeGraphRestriction G f hG ω) = finitePlaneBoolRestriction V ω := by
      funext e
      apply Bool.eq_iff_iff.mpr
      rw [← mem_boolConfigurationEquiv]
      simp only [Equiv.apply_symm_apply,Infinite.latticeGraphRestriction,
        Finset.mem_filter,Finset.mem_univ,true_and]
      have he : embeddedEdgeEmbedding G squareLattice f hG e = frozenEdgeEmbedding V e :=
        Subtype.ext rfl
      rw [he]
      rfl
    rw [hrestr]
  rw [hevent] at hcmp
  have hfree : law G θ (frozenBoundaryCondition V 0) =
      law G θ (BoundaryCondition.free ∅) :=
    law_eq_of_boundary_partition_eq θ _ _
      (by simp only [frozenBoundaryCondition,ite_true,BoundaryCondition.free])
  unfold finiteBoundaryEventProbability PD.FK.measure
  rw [hfree]
  exact hcmp

end
end PottsContinuity.RSW
