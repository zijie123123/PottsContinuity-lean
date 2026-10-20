module

public import PottsContinuity.Thm3.Prop4.MarkedBoxRawSourceIdentity
public import PottsContinuity.PD.FK.BoxTranslation

@[expose] public section

open MeasureTheory
namespace PottsContinuity.Thm3.Prop4
open PD.FK PD.RCInfinite
noncomputable section
attribute [local instance] configurationMeasurableSpace

/-- The coordinate-identical source rectangle has exactly the same finite
vertex domain as the original box, including its physical boundary. -/
theorem sourceBox_latticeRectangle_eq (n : ℕ) :
    PD.FK.latticeRectangle (-(n : ℤ),-(n : ℤ)) (2*n) (2*n) = box n := by
  ext z
  simp only [mem_latticeRectangle,box,Finset.mem_product,Finset.mem_Icc]
  omega

/-- The original physical wired partition is preserved by coordinate
transport; no full-carrier wiring is inserted. -/
theorem boxTubeRectangleIso_wired_partition (n : ℕ) :
    (boundaryConditionIso (boxTubeRectangleIso n) (frozenBoundaryCondition (box n) 1)).partition =
      (frozenBoundaryCondition (PD.FK.latticeRectangle (-(n : ℤ),-(n : ℤ)) (2*n) (2*n)) 1).partition := by
  let i := boxTubeRectangleIso n
  have hb (x : RectangleVertex (-(n : ℤ),-(n : ℤ)) (2*n) (2*n)) :
      i.symm x ∈ frozenVertexBoundary (box n) ↔
      x ∈ frozenVertexBoundary (PD.FK.latticeRectangle (-(n : ℤ),-(n : ℤ)) (2*n) (2*n)) := by
    change (i.symm x).val ∈ PD.vertexBoundary (box n) ↔ x.val ∈ PD.vertexBoundary _
    rw [boxTubeRectangleIso_symm_val]
    rw [congrArg PD.vertexBoundary (sourceBox_latticeRectangle_eq n)]
  apply Setoid.ext
  intro x y
  change (i.symm x = i.symm y ∨ i.symm x ∈ frozenVertexBoundary (box n) ∧
    i.symm y ∈ frozenVertexBoundary (box n)) ↔
    (x = y ∨ x ∈ frozenVertexBoundary _ ∧ y ∈ frozenVertexBoundary _)
  exact or_congr i.symm.injective.eq_iff (and_congr (hb x) (hb y))

/-- Every finite wired event is transported under the actual box/rectangle
isomorphism, with the unchanged original boundary partition. -/
theorem sourceBox_wired_probability_iso (n : ℕ) (θ : Parameters)
    (E : Set (Configuration (rectangleGraph (-(n : ℤ),-(n : ℤ)) (2*n) (2*n)))) :
    (PD.FK.measure (rectangleGraph (-(n : ℤ),-(n : ℤ)) (2*n) (2*n)) θ
      (frozenBoundaryCondition (PD.FK.latticeRectangle (-(n : ℤ),-(n : ℤ)) (2*n) (2*n)) 1) E).toReal =
    (PD.FK.measure (finiteLatticeGraph (box n)) θ (frozenBoundaryCondition (box n) 1)
      {B | configurationIso (boxTubeRectangleIso n) B ∈ E}).toReal := by
  let i : finiteLatticeGraph (box n) ≃g rectangleGraph (-(n : ℤ),-(n : ℤ)) (2*n) (2*n) := boxTubeRectangleIso n
  have hlaw := (law_configurationIso_map θ i (frozenBoundaryCondition (box n) 1)).trans
    (law_eq_of_boundary_partition_eq θ _ _ (boxTubeRectangleIso_wired_partition n))
  unfold PD.FK.measure
  rw [← hlaw,PMF.toMeasure_map_apply _ _ _ measurable_from_top MeasurableSpace.measurableSet_top]
  rfl

end
end PottsContinuity.Thm3.Prop4
