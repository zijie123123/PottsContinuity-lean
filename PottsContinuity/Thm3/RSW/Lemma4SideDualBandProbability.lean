module

public import PottsContinuity.Thm3.RSW.Lemma4SideInducedDualLaw
public import PottsContinuity.Thm3.RSW.Lemma4FullSideProbability

@[expose] public section

namespace PottsContinuity.RSW
open PD.FK PD.Duality MeasureTheory
noncomputable section
attribute [local instance] configurationMeasurableSpace

/-- The original source band read on every complementary dual sample via the
explicit coordinate/collar equivalence. No native path identification is
incorporated into this definition. -/
def lemma4SideInducedDualBandEvent (n : ℕ) (i : Fin 2) :
    Set (Configuration (bottomCollarInducedDualGraph (-56*(n:ℤ),0) (112*n) (54*n))) :=
  {D | inducedConfigurationExtension (lemma4SideVertices n (lemma4SideSign i))
    ((lemma4SideInducedDualEquiv n (lemma4SideSign i)
      (lemma4SideSign_eq_one_or_neg_one i)).symm D) ∈ lemma4DualBandEvent n i}

/-- The accepted sparse-side reference probability is exactly the mass of
the actual source band in the proved complementary dual law. Only the later
native path/domain identification remains, not a probabilistic law premise. -/
theorem lemma4SideReferenceProbability_eq_inducedDual (q : Set.Ici (1:ℝ))
    (n : ℕ) (i : Fin 2) :
    lemma4SideReferenceProbability (selfDualParameters q) n i =
    (measure (bottomCollarInducedDualGraph (-56*(n:ℤ),0) (112*n) (54*n)) (selfDualParameters q)
      (rectangleDualBoundaryCondition (-56*(n:ℤ),-1) (112*n) (54*n+1))
      (lemma4SideInducedDualBandEvent n i)).toReal := by
  rw [lemma4SideReferenceProbability_eq_fullSide]
  have h := congrArg (fun μ =>
    (PMF.toMeasure μ (lemma4SideInducedDualBandEvent n i)).toReal)
    (lemma4SideFull_law_map_inducedDual q n (lemma4SideSign i)
      (lemma4SideSign_eq_one_or_neg_one i))
  rw [PMF.toMeasure_map_apply _ _ _ measurable_from_top
    MeasurableSpace.measurableSet_top] at h
  simpa only [PD.FK.measure,lemma4SideInducedDualBandEvent,Set.preimage,
    Set.mem_ofPred_eq,Equiv.symm_apply_apply] using h

end
end PottsContinuity.RSW
