module

public import PottsContinuity.Thm3.Prop4.InfiniteDualArm
public import PottsContinuity.Infinite.Translation
public import PottsContinuity.PD.CorrLength.ConnectionEvents

/-!
# Whole translated arm events under frozen limits

The entire target event is translated at once. There is no union bound over
its possible terminal vertices and no loss depending on the root position.
-/

@[expose] public section

open MeasureTheory

namespace PottsContinuity.Thm3.Prop4

open PD.FK

/-- The exact frozen square-boundary arm rooted at any lattice vertex. -/
def translatedInfiniteArmEvent (x : ℤ × ℤ) (n : ℕ) : Set LatticeConfiguration :=
  {ω | ∃ z ∈ vertexBoundary (box n), (rcInfiniteOpenGraph ω).Reachable x (z+x)}

/-- Every translated whole arm is open in the original edge-state topology. -/
theorem isOpen_translatedInfiniteArmEvent (x : ℤ × ℤ) (n : ℕ) :
    IsOpen (translatedInfiniteArmEvent x n) := by
  have heq : translatedInfiniteArmEvent x n = ⋃ z ∈ vertexBoundary (box n),
      {ω : LatticeConfiguration | (rcInfiniteOpenGraph ω).Reachable x (z+x)} := by
    ext ω
    simp only [translatedInfiniteArmEvent,Set.mem_iUnion,Set.mem_ofPred_eq,exists_prop]
  rw [heq]
  exact isOpen_iUnion (fun z => isOpen_iUnion (fun _ => RSW.infinite_connection_isOpen x (z+x)))

/-- The original-state translation preimage is the complete arm at the origin. -/
theorem translatedInfiniteArmEvent_preimage (x : ℤ × ℤ) (n : ℕ) :
    latticeConfigurationTranslate x ⁻¹' translatedInfiniteArmEvent x n = RSW.infiniteArmEvent n := by
  ext ω
  have hconn (z : ℤ × ℤ) :
      (rcInfiniteOpenGraph (latticeConfigurationTranslate x ω)).Reachable x (z+x) ↔
        (rcInfiniteOpenGraph ω).Reachable (0,0) z := by
    change (PD.rcInfiniteOpenGraph (latticeConfigurationTranslate x ω)).Reachable x (z+x) ↔
      (PD.rcInfiniteOpenGraph ω).Reachable (0,0) z
    simpa only [PD.CorrLength.connectionEvent_iff_rcInfiniteReachable,latticeTranslate,
      Prod.add_def,add_comm,zero_add,add_zero] using
      PD.CorrLength.connectionEvent_translation x (0,0) z ω
  change (∃ z ∈ vertexBoundary (box n),
    (rcInfiniteOpenGraph (latticeConfigurationTranslate x ω)).Reachable x (z+x)) ↔ _
  simp only [hconn]
  rfl

/-- Frozen free or wired limits preserve the probability of the entire translated arm. -/
theorem translatedInfiniteArm_probability_eq (θ : Parameters) (i : Fin 2)
    (μ : Measure LatticeConfiguration) (hμ : IsRCInfiniteVolumeLimit θ.toP θ.toQ i μ)
    (x : ℤ × ℤ) (n : ℕ) :
    μ.real (translatedInfiniteArmEvent x n) = RSW.oneArmProbability μ n := by
  have hinv := Infinite.infinite_volume_translation_invariant θ.toP θ.toQ θ.property i μ hμ x
  have h := congrArg (fun ν : Measure LatticeConfiguration => ν (translatedInfiniteArmEvent x n)) hinv
  have hm := Measure.map_apply (μ := μ) (latticeConfigurationTranslate_measurable x)
    (isOpen_translatedInfiniteArmEvent x n).measurableSet
  have hmass : μ (RSW.infiniteArmEvent n) = μ (translatedInfiniteArmEvent x n) :=
    (congrArg μ (translatedInfiniteArmEvent_preimage x n)).symm.trans (hm.symm.trans h)
  exact (congrArg ENNReal.toReal hmass).symm

/-- Actual closed-dual arms at every face root have the same exact free one-arm probability. -/
theorem selfDual_wired_translated_dual_oneArm_probability (q : Set.Ici (1 : ℝ))
    (μ₀ μ₁ : Measure LatticeConfiguration)
    (hμ₀ : IsRCInfiniteVolumeLimit (RSW.selfDualParameters q).toP
      (RSW.selfDualParameters q).toQ 0 μ₀)
    (hμ₁ : IsRCInfiniteVolumeLimit (RSW.selfDualParameters q).toP
      (RSW.selfDualParameters q).toQ 1 μ₁) (x : ℤ × ℤ) (n : ℕ) :
    μ₁.real {ω | ∃ z ∈ vertexBoundary (box n),
      (Medial.wholePlaneClosedDualGraph ω).Reachable x (z+x)} = RSW.oneArmProbability μ₀ n := by
  have hpre : Medial.wholePlaneDualConfigurationHomeomorph ⁻¹' translatedInfiniteArmEvent x n =
      {ω | ∃ z ∈ vertexBoundary (box n),
        (Medial.wholePlaneClosedDualGraph ω).Reachable x (z+x)} := by
    ext ω
    change (∃ z ∈ vertexBoundary (box n),
      (rcInfiniteOpenGraph (Medial.wholePlaneDualConfigurationHomeomorph ω)).Reachable x (z+x)) ↔ _
    rw [← closedDualGraph_eq_frozen_dualOpenGraph ω]
    rfl
  rw [← hpre]
  exact (selfDual_wired_dual_event_probability_eq_free q μ₀ μ₁ hμ₀ hμ₁
    (translatedInfiniteArmEvent x n) (isOpen_translatedInfiniteArmEvent x n).measurableSet).trans
      (translatedInfiniteArm_probability_eq (RSW.selfDualParameters q) 0 μ₀ hμ₀ x n)

end PottsContinuity.Thm3.Prop4
