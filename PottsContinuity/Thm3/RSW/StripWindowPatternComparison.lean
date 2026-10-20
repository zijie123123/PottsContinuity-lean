module

public import PottsContinuity.Thm3.RSW.StripBoundaryPatternLimit
public import PottsContinuity.Thm3.RSW.StripWindowCutNormalization
public import PottsContinuity.PD.FK.BoundaryPartitionLaw

@[expose] public section

namespace PottsContinuity.RSW
open PD.FK MeasureTheory Filter Topology FKC.Medial
noncomputable section
attribute [local instance] configurationMeasurableSpace

/-- Both actual source lateral conventions are supported on the normalized
top and side arcs of the complete original window. -/
theorem stripWindowCutBoundary_supported (n M : ℕ) (i : Fin 2) :
    (boundaryConditionIso (stripWindowCutIso n M) (stripWindowBoundary n M i)).boundary ⊆
      FKC.FiniteFK.horizontalStripTopSidesSet M (2*n) := by
  rintro v ⟨u,hu,rfl⟩
  change u.val.2=3*(n:ℤ) ∨ i=1 ∧ (u.val.1= -(M:ℤ) ∨ u.val.1=M) at hu
  change u.val.2+(n:ℤ)= (2*(2*n):ℤ) ∨ u.val.1= -(M:ℤ) ∨ u.val.1=M
  rcases hu with hu | ⟨_,hu⟩ <;> omega

/-- The top-only normalized partition is contained in either actual
source boundary convention. -/
theorem stripWindowCutBoundary_dominates_top (n M : ℕ) (i : Fin 2) :
    (BoundaryCondition.wired (FKC.FiniteFK.horizontalStripTopWiredSet M (2*n))).partition ≤
      (boundaryConditionIso (stripWindowCutIso n M) (stripWindowBoundary n M i)).partition := by
  intro u v h
  change u=v ∨ u.val.2=(2*(2*n):ℤ) ∧ v.val.2=(2*(2*n):ℤ) at h
  change (stripWindowCutIso n M).symm u = (stripWindowCutIso n M).symm v ∨
    ((u.val.2-(n:ℤ)=3*(n:ℤ) ∨ i=1 ∧ (u.val.1= -(M:ℤ) ∨ u.val.1=M)) ∧
     (v.val.2-(n:ℤ)=3*(n:ℤ) ∨ i=1 ∧ (v.val.1= -(M:ℤ) ∨ v.val.1=M)))
  rcases h with rfl | ⟨hu,hv⟩
  · exact Or.inl rfl
  · exact Or.inr ⟨Or.inl (by omega),Or.inl (by omega)⟩

/-- Top-only wiring remains exactly top-only under the physical vertical
translation of the original full strip window. -/
theorem stripWindowCutBoundary_top_partition (n M : ℕ) :
    (boundaryConditionIso (stripWindowCutIso n M) (stripWindowBoundary n M 0)).partition =
      (BoundaryCondition.wired (FKC.FiniteFK.horizontalStripTopWiredSet M (2*n))).partition := by
  apply Setoid.ext
  intro u v
  change ((stripWindowCutIso n M).symm u = (stripWindowCutIso n M).symm v ∨
    ((u.val.2-(n:ℤ)=3*(n:ℤ) ∨ (0:Fin 2)=1 ∧ (u.val.1= -(M:ℤ) ∨ u.val.1=M)) ∧
     (v.val.2-(n:ℤ)=3*(n:ℤ) ∨ (0:Fin 2)=1 ∧ (v.val.1= -(M:ℤ) ∨ v.val.1=M)))) ↔
    (u=v ∨ u.val.2=(2*(2*n):ℤ) ∧ v.val.2=(2*(2*n):ℤ))
  rw [(stripWindowCutIso n M).symm.injective.eq_iff]
  simp only [show (0:Fin 2) ≠ 1 by decide, false_and, or_false]
  exact or_congr Iff.rfl (and_congr (by omega) (by omega))

/-- Exact probability transport of every finite pattern, preserving the
actual original window law and its specified lateral convention. -/
theorem stripWindow_normalized_pattern_probability (θ : Parameters) (n M : ℕ) (i : Fin 2)
    (O C : Finset FKC.squareLattice.edgeSet) :
    (measure (squareLattice.induce (stripWindow n M : Set (ℤ×ℤ))) θ (stripWindowBoundary n M i)
      ((configurationIso (stripWindowCutIso n M)) ⁻¹'
        stripRectanglePatternEvent M (2*n) O C)).toReal =
    (measure (horizontalStripCutRectangle M (2*n)) θ
      (boundaryConditionIso (stripWindowCutIso n M) (stripWindowBoundary n M i))).real
        (stripRectanglePatternEvent M (2*n) O C) := by
  have h := law_configurationIso_map θ (stripWindowCutIso n M) (stripWindowBoundary n M i)
  have heq := congrArg (fun ρ => (ρ.toMeasure (stripRectanglePatternEvent M (2*n) O C)).toReal) h
  rw [PMF.toMeasure_map_apply _ _ _ measurable_from_top MeasurableSpace.measurableSet_top] at heq
  exact heq

/-- Every supported original finite pattern has the same limiting
probability for top-only and top-with-ends source approximations. The
normalization is the literal whole-window translation, with all bonds kept. -/
theorem stripWindow_pattern_boundary_difference_tendsto_zero
    (θ : Parameters) (n K : ℕ) (i : Fin 2)
    (O C : Finset FKC.squareLattice.edgeSet)
    (hO : ∀ e ∈ O, e ∈ Set.range (horizontalStripRectangleOriginalEdge K (2*n)))
    (hC : ∀ e ∈ C, e ∈ Set.range (horizontalStripRectangleOriginalEdge K (2*n))) :
    Tendsto (fun M =>
      (measure (squareLattice.induce (stripWindow n M : Set (ℤ×ℤ))) θ (stripWindowBoundary n M i)
        ((configurationIso (stripWindowCutIso n M)) ⁻¹'
          stripRectanglePatternEvent M (2*n) O C)).toReal -
      (measure (squareLattice.induce (stripWindow n M : Set (ℤ×ℤ))) θ (stripWindowBoundary n M 0)
        ((configurationIso (stripWindowCutIso n M)) ⁻¹'
          stripRectanglePatternEvent M (2*n) O C)).toReal) atTop (𝓝 0) := by
  have h := strip_pattern_boundary_difference_tendsto_zero θ (2*n) K
    (fun M => boundaryConditionIso (stripWindowCutIso n M) (stripWindowBoundary n M i))
    (fun M => stripWindowCutBoundary_supported n M i)
    (fun M => stripWindowCutBoundary_dominates_top n M i) O C hO hC
  convert h using 1
  funext M
  rw [stripWindow_normalized_pattern_probability,stripWindow_normalized_pattern_probability]
  have heq := law_eq_of_boundary_partition_eq (G:=horizontalStripCutRectangle M (2*n)) θ _ _
    (stripWindowCutBoundary_top_partition n M)
  have heq' := congrArg (fun ρ => (ρ.toMeasure (stripRectanglePatternEvent M (2*n) O C)).toReal) heq
  exact congrArg (fun x => (measure (horizontalStripCutRectangle M (2*n)) θ
    (boundaryConditionIso (stripWindowCutIso n M) (stripWindowBoundary n M i))).real
      (stripRectanglePatternEvent M (2*n) O C) - x) heq'

end
end PottsContinuity.RSW
