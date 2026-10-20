module

public import PottsContinuity.Infinite.Bridge
public import PottsContinuity.Infinite.Parameters
public import PottsContinuity.PD.FK.WiredBoxLimits
public import PottsContinuity.PD.FK.WiredBoxLaw
public import PottsContinuity.PD.FK.IncreasingEvents
public import PottsContinuity.PD.Duality.FreeAssociation

/-! FKG for increasing clopen events under free and wired limits. -/

@[expose] public section

open MeasureTheory Filter Topology

namespace PottsContinuity.Infinite

open PottsContinuity
open PottsContinuity.PD
open PottsContinuity.PD.FK
open PottsContinuity.PD.Duality

noncomputable section

private theorem frozen_limit_to_pd
    (p : Set.Icc (0 : ℝ) 1) (q : Set.Ioi (0 : ℝ))
    (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1) (hq : 1 ≤ (q : ℝ))
    (i : Fin 2) (μ : Measure (squareLattice.edgeSet → Bool))
    (hμ : PottsContinuity.IsRCInfiniteVolumeLimit p q i μ) :
    PottsContinuity.PD.IsRCInfiniteVolumeLimit
      (pdParameters p q hp0 hp1 hq).toP (pdParameters p q hp0 hp1 hq).toQ i μ := by
  simpa only [pdParameters_toP, pdParameters_toQ] using
    isRCInfiniteVolumeLimit_to_PD_box p q i μ hμ

private theorem wiredBoxConfiguration_mono (c : LatticeVertex) (r : ℕ)
    {A B : Configuration (boxGraph c r)} (hAB : A ≤ B) :
    wiredBoxConfiguration c r A ≤ wiredBoxConfiguration c r B := by
  classical
  intro e
  by_cases he : e ∈ Set.range (boxEdgeEmbedding c r)
  · obtain ⟨f, hf⟩ := he
    rw [← hf, wiredBoxConfiguration_at, wiredBoxConfiguration_at]
    by_cases hA : f ∈ A
    · have hB := hAB hA
      simp [hA, hB]
    · simp [hA]
  · rw [wiredBoxConfiguration_outside c r A e he,
      wiredBoxConfiguration_outside c r B e he]

private theorem wiredBoxProbabilityMeasure_apply_preimage
    (θ : Parameters) (c : LatticeVertex) (r : ℕ)
    (s : Set LatticeConfiguration) (hs : MeasurableSet s) :
    (wiredBoxProbabilityMeasure θ c r : Measure LatticeConfiguration) s =
      measure (boxGraph c r) θ (BoundaryCondition.wired (boxVertexBoundary c r))
        {A | wiredBoxConfiguration c r A ∈ s} := by
  change ((law (boxGraph c r) θ (BoundaryCondition.wired (boxVertexBoundary c r))).map
    (wiredBoxConfiguration c r)).toMeasure s = _
  rw [PMF.toMeasure_map_apply _ _ _ measurable_from_top hs]
  rfl

private theorem wiredBoxProbabilityMeasure_finite_positive_association
    (θ : Parameters) (c : LatticeVertex) (r : ℕ)
    (s t : Set LatticeConfiguration) (hsUpper : IsUpperSet s)
    (htUpper : IsUpperSet t) (hsMeas : MeasurableSet s) (htMeas : MeasurableSet t) :
    (wiredBoxProbabilityMeasure θ c r : Measure LatticeConfiguration).real s *
      (wiredBoxProbabilityMeasure θ c r : Measure LatticeConfiguration).real t ≤
        (wiredBoxProbabilityMeasure θ c r : Measure LatticeConfiguration).real (s ∩ t) := by
  let sbox : Set (Configuration (boxGraph c r)) :=
    {A | wiredBoxConfiguration c r A ∈ s}
  let tbox : Set (Configuration (boxGraph c r)) :=
    {A | wiredBoxConfiguration c r A ∈ t}
  have hsbox : IsUpperSet sbox := by
    intro A B hAB hA
    exact hsUpper (wiredBoxConfiguration_mono c r hAB) hA
  have htbox : IsUpperSet tbox := by
    intro A B hAB hA
    exact htUpper (wiredBoxConfiguration_mono c r hAB) hA
  have h := measure_positive_association θ
    (BoundaryCondition.wired (boxVertexBoundary c r)) sbox tbox hsbox htbox
  have hS := wiredBoxProbabilityMeasure_apply_preimage θ c r s hsMeas
  have hT := wiredBoxProbabilityMeasure_apply_preimage θ c r t htMeas
  have hST := wiredBoxProbabilityMeasure_apply_preimage θ c r (s ∩ t)
    (hsMeas.inter htMeas)
  have hsets : sbox ∩ tbox = {A | wiredBoxConfiguration c r A ∈ s ∩ t} := by
    ext A
    simp [sbox, tbox]
  rw [Measure.real_def, Measure.real_def, Measure.real_def]
  rw [hS, hT, hST]
  rw [hsets] at h
  exact h

private theorem wiredBoxLimit_clopen_positive_association
    (θ : Parameters) (s t : Set LatticeConfiguration)
    (hsClopen : IsClopen s) (htClopen : IsClopen t)
    (hsUpper : IsUpperSet s) (htUpper : IsUpperSet t) :
    (((Classical.choose (wiredBoxLimit_existsUnique θ) s : NNReal) : ℝ)) *
      (((Classical.choose (wiredBoxLimit_existsUnique θ) t : NNReal) : ℝ)) ≤
        (((Classical.choose (wiredBoxLimit_existsUnique θ) (s ∩ t) : NNReal) : ℝ)) := by
  let μ : ProbabilityMeasure LatticeConfiguration :=
    Classical.choose (wiredBoxLimit_existsUnique θ)
  have hweak : Tendsto (fun n => wiredBoxProbabilityMeasure θ (0, 0) n) atTop (𝓝 μ) :=
    (Classical.choose_spec (wiredBoxLimit_existsUnique θ)).1
      (fun _ => (0, 0)) (fun n => n) origin_latticeBox_nested origin_latticeBox_exhaustive
  have hS : Tendsto (fun n => wiredBoxProbabilityMeasure θ (0, 0) n s) atTop
      (𝓝 (μ s)) :=
    ProbabilityMeasure.tendsto_measure_of_isClopen_of_tendsto hweak hsClopen
  have hT : Tendsto (fun n => wiredBoxProbabilityMeasure θ (0, 0) n t) atTop
      (𝓝 (μ t)) :=
    ProbabilityMeasure.tendsto_measure_of_isClopen_of_tendsto hweak htClopen
  have hST : Tendsto (fun n => wiredBoxProbabilityMeasure θ (0, 0) n (s ∩ t)) atTop
      (𝓝 (μ (s ∩ t))) :=
    ProbabilityMeasure.tendsto_measure_of_isClopen_of_tendsto hweak
      (hsClopen.inter htClopen)
  have hSreal : Tendsto (fun n =>
      (((wiredBoxProbabilityMeasure θ (0, 0) n : ProbabilityMeasure LatticeConfiguration) s : NNReal) : ℝ))
      atTop (𝓝 ((μ s : NNReal) : ℝ)) :=
    (NNReal.continuous_coe.continuousAt.tendsto).comp hS
  have hTreal : Tendsto (fun n =>
      (((wiredBoxProbabilityMeasure θ (0, 0) n : ProbabilityMeasure LatticeConfiguration) t : NNReal) : ℝ))
      atTop (𝓝 ((μ t : NNReal) : ℝ)) :=
    (NNReal.continuous_coe.continuousAt.tendsto).comp hT
  have hSTreal : Tendsto (fun n =>
      (((wiredBoxProbabilityMeasure θ (0, 0) n : ProbabilityMeasure LatticeConfiguration)
        (s ∩ t) : NNReal) : ℝ)) atTop (𝓝 ((μ (s ∩ t) : NNReal) : ℝ)) :=
    (NNReal.continuous_coe.continuousAt.tendsto).comp hST
  have hprod : Tendsto (fun n =>
      (((wiredBoxProbabilityMeasure θ (0, 0) n : ProbabilityMeasure LatticeConfiguration) s : NNReal) : ℝ) *
        (((wiredBoxProbabilityMeasure θ (0, 0) n : ProbabilityMeasure LatticeConfiguration) t : NNReal) : ℝ))
      atTop (𝓝 (((μ s : NNReal) : ℝ) * ((μ t : NNReal) : ℝ))) := hSreal.mul hTreal
  have hfinite (n : ℕ) :
      (((wiredBoxProbabilityMeasure θ (0, 0) n : ProbabilityMeasure LatticeConfiguration) s : NNReal) : ℝ) *
        (((wiredBoxProbabilityMeasure θ (0, 0) n : ProbabilityMeasure LatticeConfiguration) t : NNReal) : ℝ) ≤
          (((wiredBoxProbabilityMeasure θ (0, 0) n : ProbabilityMeasure LatticeConfiguration)
            (s ∩ t) : NNReal) : ℝ) := by
    have h := wiredBoxProbabilityMeasure_finite_positive_association θ (0, 0) n s t
      hsUpper htUpper hsClopen.2.measurableSet htClopen.2.measurableSet
    simpa [ProbabilityMeasure.measureReal_eq_coe_coeFn] using h
  have hlimit := le_of_tendsto_of_tendsto' hprod hSTreal hfinite
  simpa [μ] using hlimit

private theorem wired_limit_eq_selected
    (θ : Parameters) (μ : Measure LatticeConfiguration)
    (hμ : PottsContinuity.PD.IsRCInfiniteVolumeLimit θ.toP θ.toQ 1 μ) :
    μ = (Classical.choose (wiredBoxLimit_existsUnique θ)).toMeasure := by
  let ν := Classical.choose (wiredBoxLimit_existsUnique θ)
  have hν := (Classical.choose_spec (wiredBoxLimit_existsUnique θ)).1
    (fun _ => (0, 0)) (fun n => n) origin_latticeBox_nested origin_latticeBox_exhaustive
  exact PottsContinuity.PD.rc_limit_unique θ.toP θ.toQ 1 μ ν.toMeasure hμ
    (isRCInfiniteVolumeLimit_of_wiredBox_tendsto θ ν hν)

private theorem wired_limit_clopen_positive_association
    (θ : Parameters) (μ : Measure LatticeConfiguration)
    (hμ : PottsContinuity.PD.IsRCInfiniteVolumeLimit θ.toP θ.toQ 1 μ)
    (s t : Set LatticeConfiguration) (hs : IsClopen s) (ht : IsClopen t)
    (hsu : IsUpperSet s) (htu : IsUpperSet t) :
    μ s * μ t ≤ μ (s ∩ t) := by
  have := hμ.1
  apply (ENNReal.toReal_le_toReal
    (ENNReal.mul_ne_top (measure_ne_top μ s) (measure_ne_top μ t))
    (measure_ne_top μ (s ∩ t))).1
  rw [ENNReal.toReal_mul, wired_limit_eq_selected θ μ hμ]
  simpa only [← ProbabilityMeasure.measureReal_eq_coe_coeFn, Measure.real_def] using
    wiredBoxLimit_clopen_positive_association θ s t hs ht hsu htu

/-- FKG inequality for measurable increasing events under the free limit, in
the clopen case. -/
theorem free_infinite_FKG_clopen
    (p : Set.Icc (0 : ℝ) 1) (q : Set.Ioi (0 : ℝ))
    (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1) (hq : 1 ≤ (q : ℝ))
    (μ : Measure (squareLattice.edgeSet → Bool))
    (hμ : PottsContinuity.IsRCInfiniteVolumeLimit p q 0 μ)
    (s t : Set LatticeConfiguration) (hs : IsClopen s) (ht : IsClopen t)
    (hsu : IsUpperSet s) (htu : IsUpperSet t) :
    μ s * μ t ≤ μ (s ∩ t) := by
  exact free_clopen_positive_association (pdParameters p q hp0 hp1 hq) μ
    (frozen_limit_to_pd p q hp0 hp1 hq 0 μ hμ) s t hs ht hsu htu

/-- FKG inequality for measurable increasing events under the wired limit, in
the clopen case. -/
theorem wired_infinite_FKG_clopen
    (p : Set.Icc (0 : ℝ) 1) (q : Set.Ioi (0 : ℝ))
    (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1) (hq : 1 ≤ (q : ℝ))
    (μ : Measure (squareLattice.edgeSet → Bool))
    (hμ : PottsContinuity.IsRCInfiniteVolumeLimit p q 1 μ)
    (s t : Set LatticeConfiguration) (hs : IsClopen s) (ht : IsClopen t)
    (hsu : IsUpperSet s) (htu : IsUpperSet t) :
    μ s * μ t ≤ μ (s ∩ t) := by
  exact wired_limit_clopen_positive_association (pdParameters p q hp0 hp1 hq) μ
    (frozen_limit_to_pd p q hp0 hp1 hq 1 μ hμ) s t hs ht hsu htu

end
end PottsContinuity.Infinite
