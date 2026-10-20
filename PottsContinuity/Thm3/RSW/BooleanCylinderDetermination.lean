module

public import Mathlib.MeasureTheory.Constructions.Cylinders
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

@[expose] public section

namespace PottsContinuity.RSW
open Set MeasureTheory
noncomputable section

-- Generalized from PD/FK/CylinderDetermination: the edge index is arbitrary.
/-- Finite all-open events determine a probability law on Boolean coordinates. -/
theorem boolean_measure_eq_of_allOpen {ι : Type*} (μ ν : Measure (ι → Bool))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (h : ∀ F : Finset ι, μ {ω | ∀ e ∈ F, ω e = true} =
      ν {ω | ∀ e ∈ F, ω e = true}) : μ = ν := by
  classical
  let C : Set (Set (ι → Bool)) := {s | ∃ F : Finset ι, {ω | ∀ e ∈ F, ω e = true} = s}
  have hpi : IsPiSystem C := by
    rintro s ⟨F, rfl⟩ t ⟨G, rfl⟩ _
    refine ⟨F ∪ G, ?_⟩
    ext ω
    simp only [mem_ofPred_eq, Finset.mem_union, mem_inter_iff]
    exact ⟨fun h => ⟨fun e he => h e (Or.inl he), fun e he => h e (Or.inr he)⟩,
      fun h e he => he.elim (h.1 e) (h.2 e)⟩
  have hgen : MeasurableSpace.generateFrom C = (MeasurableSpace.pi : MeasurableSpace (ι → Bool)) := by
    apply le_antisymm
    · refine MeasurableSpace.generateFrom_le fun s hs => ?_
      rcases hs with ⟨F, rfl⟩
      induction F using Finset.induction_on with
      | empty => simp
      | @insert e F he ih =>
        have heq : {ω : ι → Bool | ∀ j ∈ insert e F, ω j = true} =
            {ω | ω e = true} ∩ {ω | ∀ j ∈ F, ω j = true} := by ext ω; simp
        rw [heq]
        exact (measurable_pi_apply e (measurableSet_singleton true)).inter ih
    · rw [MeasurableSpace.pi]
      refine iSup_le fun e => ?_
      change MeasurableSpace.comap (fun ω : ι → Bool => ω e)
        (inferInstance : MeasurableSpace Bool) ≤ MeasurableSpace.generateFrom C
      let booleanCylinderGeneratedSpace : MeasurableSpace (ι → Bool) :=
        MeasurableSpace.generateFrom C
      have hf : Measurable (fun ω : ι → Bool => ω e) :=
        measurable_to_bool (by
          apply MeasurableSpace.measurableSet_generateFrom
          exact ⟨{e}, by ext ω; simp⟩)
      exact hf.comap_le
  exact @ext_of_generate_finite (ι → Bool) MeasurableSpace.pi μ ν C hgen.symm hpi
    (inferInstance : IsFiniteMeasure μ)
    (fun s hs => by rcases hs with ⟨F, rfl⟩; exact h F) (by simp)

end
end PottsContinuity.RSW
