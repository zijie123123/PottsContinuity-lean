module

public import PottsContinuity.Thm3.RSW.BoxCorridors
public import PottsContinuity.Foundations.BoxBoundary
public import PottsContinuity.PD.FK.BoundaryPartitionLaw

@[expose] public section

namespace PottsContinuity.RSW
open PD.FK MeasureTheory
noncomputable section
attribute [local instance] configurationMeasurableSpace

/-- Coordinate exchange preserves the exact frozen wired partition of a box. -/
theorem boxCoordinateSwap_frozen_wired_partition (N : ℕ) :
    (boundaryConditionIso (boxCoordinateSwapIso N)
      (frozenBoundaryCondition (box N) 1)).partition =
      (frozenBoundaryCondition (box N) 1).partition := by
  have hb (u : (box N : Set LatticeVertex)) :
      u ∈ frozenVertexBoundary (box N) ↔ max |u.val.1| |u.val.2| = (N:ℤ) := by
    change u.val ∈ PD.vertexBoundary (box N) ↔ _
    rw [← Foundations.vertexBoundary_eq_PD,Foundations.vertexBoundary_box_eq]
    rfl
  apply Setoid.ext
  intro u v
  change ((boxCoordinateSwapIso N).symm u = (boxCoordinateSwapIso N).symm v ∨
      (boxCoordinateSwapIso N).symm u ∈ frozenVertexBoundary (box N) ∧
      (boxCoordinateSwapIso N).symm v ∈ frozenVertexBoundary (box N)) ↔
    (u = v ∨ u ∈ frozenVertexBoundary (box N) ∧ v ∈ frozenVertexBoundary (box N))
  simp only [hb]
  change ((boxCoordinateSwapIso N).symm u = (boxCoordinateSwapIso N).symm v ∨
      max |u.val.2| |u.val.1| = (N:ℤ) ∧ max |v.val.2| |v.val.1| = (N:ℤ)) ↔
    (u = v ∨ max |u.val.1| |u.val.2| = (N:ℤ) ∧ max |v.val.1| |v.val.2| = (N:ℤ))
  rw [max_comm |u.val.2| |u.val.1|,max_comm |v.val.2| |v.val.1|]
  exact or_congr (boxCoordinateSwapIso N).symm.injective.eq_iff Iff.rfl

/-- Every actual finite wired-box event transports exactly by coordinate
exchange; no invariance of translated ambient boxes is asserted. -/
theorem finite_wired_box_probability_swap (θ : Parameters) (N : ℕ)
    (E : ((squareLattice.induce (box N : Set LatticeVertex)).edgeSet → Bool) → Prop) :
    finiteBoundaryEventProbability (box N) θ (frozenBoundaryCondition (box N) 1) E =
      finiteBoundaryEventProbability (box N) θ (frozenBoundaryCondition (box N) 1)
        (fun ω => E (finiteBoolIso (box N) (box N) (boxCoordinateSwapIso N) ω)) := by
  have hlaw := law_configurationIso_map θ (boxCoordinateSwapIso N)
    (frozenBoundaryCondition (box N) 1)
  have heq := law_eq_of_boundary_partition_eq (G := squareLattice.induce (box N : Set LatticeVertex)) θ _ _
    (boxCoordinateSwap_frozen_wired_partition N)
  rw [heq] at hlaw
  unfold finiteBoundaryEventProbability PD.FK.measure
  conv_lhs =>
    rw [← hlaw,PMF.toMeasure_map_apply _ _ _ measurable_from_top MeasurableSpace.measurableSet_top]
  congr 2
  ext A
  simp only [finiteBoolEvent,finiteBoolIso,Set.mem_ofPred_eq,
    Equiv.trans_apply,Equiv.apply_symm_apply]
  rfl

end
end PottsContinuity.RSW
