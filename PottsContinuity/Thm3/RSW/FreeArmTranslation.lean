module

public import PottsContinuity.Thm3.RSW.ArmOpen
public import PottsContinuity.Thm3.Easy.P2ToP3WeakRSW

@[expose] public section

namespace PottsContinuity.RSW
open MeasureTheory PD.FK PD.CorrLength Thm3.Easy
noncomputable section

/-- PD's centered boundary arm event is exactly the frozen arm event. -/
theorem oneArmBoundaryEvent_zero_eq (n : ℕ) :
    Thm3.Easy.oneArmBoundaryEvent (0,0) n = infiniteArmEvent n := by
  have hb : latticeBox (0,0) n = box n := by
    simp only [latticeBox,box,zero_sub,zero_add]
  ext ω
  simp only [Thm3.Easy.oneArmBoundaryEvent,infiniteArmEvent,hb,
    Foundations.vertexBoundary_eq_PD,Set.mem_ofPred_eq,
    PD.CorrLength.connectionEvent_iff_rcInfiniteReachable,
    Foundations.rcInfiniteOpenGraph_eq_PD]
  rfl

-- Generalises the wired-only `Thm3.Easy.oneArmBoundaryEvent_real_translation` to both limit laws.
theorem oneArmBoundaryEvent_real_translation_of_limit
    (p : Set.Icc (0 : ℝ) 1) (q : Set.Ioi (0 : ℝ))
    (hq : 1 ≤ (q : ℝ)) (μ : Measure LatticeConfiguration)
    (i : Fin 2) (hμ : IsRCInfiniteVolumeLimit p q i μ)
    (a x : LatticeVertex) (n : ℕ) :
    μ.real (oneArmBoundaryEvent (latticeTranslate a x) n) =
      μ.real (oneArmBoundaryEvent x n) := by
  let : IsProbabilityMeasure μ := hμ.1
  have hinv := Infinite.infinite_volume_translation_invariant p q hq i μ hμ a
  have hmap := congrArg
    (fun ν : Measure LatticeConfiguration =>
      ν (oneArmBoundaryEvent (latticeTranslate a x) n)) hinv
  have hmap_apply :
      (μ.map (latticeConfigurationTranslate a))
        (oneArmBoundaryEvent (latticeTranslate a x) n) =
      μ ((latticeConfigurationTranslate a) ⁻¹'
        oneArmBoundaryEvent (latticeTranslate a x) n) :=
    Measure.map_apply (latticeConfigurationTranslate_measurable a)
      (oneArmBoundaryEvent_measurable (latticeTranslate a x) n)
  have hpre : (latticeConfigurationTranslate a) ⁻¹'
      oneArmBoundaryEvent (latticeTranslate a x) n = oneArmBoundaryEvent x n := by
    ext ω
    exact oneArmBoundaryEvent_translation a x n ω
  have hprob : μ (oneArmBoundaryEvent x n) =
      μ (oneArmBoundaryEvent (latticeTranslate a x) n) := by
    calc
      μ (oneArmBoundaryEvent x n) =
          μ ((latticeConfigurationTranslate a) ⁻¹'
            oneArmBoundaryEvent (latticeTranslate a x) n) := by rw [hpre]
      _ = (μ.map (latticeConfigurationTranslate a))
          (oneArmBoundaryEvent (latticeTranslate a x) n) := hmap_apply.symm
      _ = μ (oneArmBoundaryEvent (latticeTranslate a x) n) := hmap
  have hreal := congrArg ENNReal.toReal hprob
  simpa [Measure.real_def] using hreal.symm

/-- Every translated arm has the exact frozen root-arm probability under a
free infinite-volume limit, at independent interior parameters. -/
theorem free_oneArmBoundaryEvent_real_eq (θ : Parameters)
    (μ : Measure LatticeConfiguration) (hμ : IsRCInfiniteVolumeLimit θ.toP θ.toQ 0 μ)
    (x : LatticeVertex) (n : ℕ) :
    μ.real (Thm3.Easy.oneArmBoundaryEvent x n) = oneArmProbability μ n := by
  have h := oneArmBoundaryEvent_real_translation_of_limit θ.toP θ.toQ θ.property
    μ 0 hμ x (0,0) n
  have hx : latticeTranslate x (0,0) = x := by
    simp only [latticeTranslate,zero_add,Prod.eta]
  rw [hx,oneArmBoundaryEvent_zero_eq] at h
  exact h

/-- A connection leaving the centered box reaches its genuine vertex boundary. -/
theorem connectionEvent_subset_oneArmBoundaryEvent (x y : LatticeVertex) (n : ℕ)
    (hy : y ∉ latticeBox x n) :
    PD.CorrLength.connectionEvent x y ⊆ Thm3.Easy.oneArmBoundaryEvent x n := by
  intro ω hω
  obtain ⟨p⟩ := (PD.CorrLength.connectionEvent_iff_rcInfiniteReachable x y ω).mp hω
  obtain ⟨z,hz,q,_hq,w,hzw,hw⟩ :=
    PD.RCInfinite.walk_prefix_to_boundary p (center_mem_latticeBox x n) hy
  refine ⟨z,⟨hz,w,?_,hw⟩,?_⟩
  · exact squareLattice.mem_edgeSet.mp ((PD.RCInfinite.rcInfiniteOpenGraph_adj ω z w).mp hzw).1
  · exact (PD.CorrLength.connectionEvent_iff_rcInfiniteReachable x z ω).mpr q.reachable

end
end PottsContinuity.RSW
