module

public import PottsContinuity.Thm3.RSW.StripAsymmetricBoundaryComparison
public import PottsContinuity.Thm3.RSW.StripWeakCylinderCriterion
public import PottsContinuity.Thm3.RSW.StripLateralIndependence
public import PottsContinuity.Thm3.RSW.StripEvents

@[expose] public section

namespace PottsContinuity.RSW
open PD.FK MeasureTheory Filter Topology
noncomputable section
attribute [local instance] configurationMeasurableSpace

/-- Literal finite-window extension, read on every original infinite-strip
coordinate; all bonds outside the sampled centered window are closed. -/
def stripWindowOriginalRead (n M : ℕ)
    (C : Configuration (squareLattice.induce (stripWindow n M : Set (ℤ×ℤ)))) : StripConfiguration n :=
  stripPlaneRestriction n (stripWindowPlaneConfiguration n M C)

/-- Probability law of the actual centered-window read, with its original
source lateral convention retained. -/
def stripWindowReadProbabilityMeasure (θ : Parameters) (n : ℕ) (i : Fin 2) (M : ℕ) :
    ProbabilityMeasure (StripConfiguration n) :=
  ⟨((law (squareLattice.induce (stripWindow n M : Set (ℤ×ℤ))) θ
    (stripWindowBoundary n M i)).map (stripWindowOriginalRead n M)).toMeasure,
    PMF.toMeasure.isProbabilityMeasure _⟩

/-- Read the centered source window from the actual asymmetric sample.
The extra left column is integrated out, rather than assigned a sampled state. -/
def stripAsymmetricCenteredRead (n M : ℕ)
    (C : Configuration (rectangleGraph (-(M:ℤ)-1,-(n:ℤ)) (2*M+1) (4*n))) : StripConfiguration n :=
  stripWindowOriginalRead n M (embeddedConfigurationRestriction
    (squareLattice.induce (stripWindow n M : Set (ℤ×ℤ)))
    (rectangleGraph (-(M:ℤ)-1,-(n:ℤ)) (2*M+1) (4*n))
    (stripWindowAsymmetricEmbedding n M) (stripWindowAsymmetric_map_le n M) C)

/-- The actual asymmetric top/ends law viewed through its original centered
read; every fixed original strip bond is eventually in that read. -/
def stripAsymmetricCenteredProbabilityMeasure (θ : Parameters) (n M : ℕ) :
    ProbabilityMeasure (StripConfiguration n) :=
  ⟨((law (rectangleGraph (-(M:ℤ)-1,-(n:ℤ)) (2*M+1) (4*n)) θ
    (stripAsymmetricTopSidesBoundary n M)).map (stripAsymmetricCenteredRead n M)).toMeasure,
    PMF.toMeasure.isProbabilityMeasure _⟩

/-- Every literal finite original-edge pattern is clopen. -/
theorem stripCoordinatePattern_isClopen (n : ℕ) (A : Finset (stripGraph n).edgeSet)
    (ξ : StripConfiguration n) : IsClopen {ω : StripConfiguration n | ∀ e ∈ A, ω e=ξ e} := by
  apply strip_isClopen_of_finite_support n A
  intro ω η hagree
  change (∀ e ∈ A, ω e=ξ e) ↔ (∀ e ∈ A, η e=ξ e)
  exact forall_congr' fun e => forall_congr' fun he => by rw [hagree e he]

/-- All-open source cylinders are clopen on the natural strip product space. -/
theorem stripCoordinateAllOpen_isClopen (n : ℕ) (A : Finset (stripGraph n).edgeSet) :
    IsClopen (stripCoordinateAllOpen n A) := stripCoordinatePattern_isClopen n A (fun _ => true)

/-- All-open source cylinders are increasing in the original sampled states. -/
theorem stripCoordinateAllOpen_isUpperSet (n : ℕ) (A : Finset (stripGraph n).edgeSet) :
    IsUpperSet (stripCoordinateAllOpen n A) := by
  intro ω η h hω e he
  exact Bool.le_iff_imp.mp (h e) (hω e he)

/-- Exact original-window event probability, including arbitrary finite
closed-edge patterns once their original support is present. -/
theorem stripWindowReadProbabilityMeasure_apply (θ : Parameters) (n : ℕ) (i : Fin 2) (M : ℕ)
    (E : Set (StripConfiguration n)) (hE : MeasurableSet E) :
    (stripWindowReadProbabilityMeasure θ n i M).toMeasure.real E =
      (measure (squareLattice.induce (stripWindow n M : Set (ℤ×ℤ))) θ (stripWindowBoundary n M i)
        {C | stripWindowOriginalRead n M C ∈ E}).toReal := by
  change (((law (squareLattice.induce (stripWindow n M : Set (ℤ×ℤ))) θ
    (stripWindowBoundary n M i)).map (stripWindowOriginalRead n M)).toMeasure E).toReal = _
  rw [PMF.toMeasure_map_apply _ _ _ measurable_from_top hE]
  rfl

/-- Exact asymmetric event probability after the actual centered restriction. -/
theorem stripAsymmetricCenteredProbabilityMeasure_apply (θ : Parameters) (n M : ℕ)
    (E : Set (StripConfiguration n)) (hE : MeasurableSet E) :
    (stripAsymmetricCenteredProbabilityMeasure θ n M).toMeasure.real E =
      (measure (rectangleGraph (-(M:ℤ)-1,-(n:ℤ)) (2*M+1) (4*n)) θ
        (stripAsymmetricTopSidesBoundary n M) {C | stripAsymmetricCenteredRead n M C ∈ E}).toReal := by
  change (((law (rectangleGraph (-(M:ℤ)-1,-(n:ℤ)) (2*M+1) (4*n)) θ
    (stripAsymmetricTopSidesBoundary n M)).map (stripAsymmetricCenteredRead n M)).toMeasure E).toReal = _
  rw [PMF.toMeasure_map_apply _ _ _ measurable_from_top hE]
  rfl

/-- The source cylinder read is literal, with no arbitrary values substituted
on any original bond in the pattern. -/
theorem stripWindowReadProbabilityMeasure_pattern (θ : Parameters) (n : ℕ) (i : Fin 2) (M : ℕ)
    (A : Finset (stripGraph n).edgeSet) (ξ : StripConfiguration n)
    (hsupp : ∀ e ∈ A, ∃ f : (squareLattice.induce (stripWindow n M : Set (ℤ×ℤ))).edgeSet,
      Sym2.map Subtype.val f.val=Sym2.map Subtype.val e.val) :
    (stripWindowReadProbabilityMeasure θ n i M).toMeasure.real {ω | ∀ e ∈ A, ω e=ξ e} =
      stripWindowCylinderProbability θ n i M A ξ := by
  rw [stripWindowReadProbabilityMeasure_apply _ _ _ _ _
    (stripCoordinatePattern_isClopen n A ξ).isOpen.measurableSet]
  have hset : {C | stripWindowOriginalRead n M C ∈ {ω | ∀ e ∈ A, ω e=ξ e}} =
      finiteBoolEvent (stripWindow n M) (stripWindowCylinder n M A ξ) := by
    ext C
    exact stripWindowPlanePattern_iff n M A ξ hsupp C
  unfold stripWindowCylinderProbability finiteBoundaryEventProbability
  rw [hset]

/-- Every original increasing strip event is squeezed between the two
actual centered lateral conventions, at every finite asymmetric volume. -/
theorem stripAsymmetricCentered_probability_sandwich (θ : Parameters) (n M : ℕ)
    (E : Set (StripConfiguration n)) (hE : MeasurableSet E) (hupper : IsUpperSet E) :
    (stripWindowReadProbabilityMeasure θ n 0 M).toMeasure.real E ≤
      (stripAsymmetricCenteredProbabilityMeasure θ n M).toMeasure.real E ∧
    (stripAsymmetricCenteredProbabilityMeasure θ n M).toMeasure.real E ≤
      (stripWindowReadProbabilityMeasure θ n 1 M).toMeasure.real E := by
  rw [stripWindowReadProbabilityMeasure_apply _ _ _ _ _ hE,
    stripWindowReadProbabilityMeasure_apply _ _ _ _ _ hE,
    stripAsymmetricCenteredProbabilityMeasure_apply _ _ _ _ hE]
  apply stripAsymmetric_boundary_probability_sandwich n M θ
    {C | stripWindowOriginalRead n M C ∈ E}
  intro C D hCD hC
  apply hupper ?_ hC
  intro e
  exact stripWindowPlaneConfiguration_mono n M hCD ((stripPlaneEmbedding n).mapEdgeSet e)

end
end PottsContinuity.RSW
