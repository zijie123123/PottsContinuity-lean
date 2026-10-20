module

public import PottsContinuity.BD12.KSTProbability
public import PottsContinuity.BD12.KSTEventRegularity
public import PottsContinuity.BD12.KSTHypotheses
public import PottsContinuity.PlanarTopology.KSTPartition
public import PottsContinuity.PlanarTopology.KSTClosing

/-! Actual wired-law cascade and closing, conditional on the remaining
deterministic inclusions. The partition premise is discharged by
`PlanarTopology.kst_quasi_partition`. -/

@[expose] public section

namespace PottsContinuity.BD12

open MeasureTheory PD.FK

/-- Image translation of an event, written as the inverse-translation preimage. -/
abbrev kstTranslateEvent (a : LatticeVertex) (A : Set LatticeConfiguration) :=
  latticeConfigurationTranslate (-a) ⁻¹' A

theorem wired_kstTranslateEvent_probability (θ : Parameters)
    (μ : Measure LatticeConfiguration)
    (hμ : IsRCInfiniteVolumeLimit θ.toP θ.toQ 1 μ)
    (a : LatticeVertex) {A : Set LatticeConfiguration} (hA : MeasurableSet A) :
    μ.real (kstTranslateEvent a A) = μ.real A := by
  have h := wired_translation_invariant θ μ hμ (-a)
  have he := congrArg (fun ν : Measure LatticeConfiguration => ν A) h
  rw [Measure.map_apply (latticeConfigurationTranslate_measurable (-a)) hA] at he
  exact congrArg ENNReal.toReal he

theorem kstTranslateEvent_measurable (a : LatticeVertex)
    {A : Set LatticeConfiguration} (hA : MeasurableSet A) :
    MeasurableSet (kstTranslateEvent a A) :=
  hA.preimage (latticeConfigurationTranslate_measurable (-a))

theorem kstTranslateEvent_isUpperSet (a : LatticeVertex)
    {A : Set LatticeConfiguration} (hA : IsUpperSet A) :
    IsUpperSet (kstTranslateEvent a A) := by
  intro ω η hωη hω
  apply hA _ hω
  intro e
  simp only [latticeConfigurationTranslate_apply]
  exact hωη _

/-- Source Lemma third-relation for the actual wired measure. Only the exact
corridor-to-bridge inclusion remains conditional; the partition is
`PlanarTopology.kst_quasi_partition`. -/
theorem wired_kst_cascade_of_kstCorridor (θ : Parameters)
    (μ : Measure LatticeConfiguration)
    (hμ : IsRCInfiniteVolumeLimit θ.toP θ.toQ 1 μ)
    (m l k : ℕ) (hml : l ≤ m) (hlk : k ≤ l) (hk : 1 ≤ k)
    (hcorridor : kstAvoidingPath l k ∩ kstQuasiCrossing l k ⊆
      kstTranslateEvent (-((l / 6 : ℕ) : ℤ), 0) (kstBridge l) ∪
      kstTranslateEvent (((l / 6 : ℕ) : ℤ), 0) (kstBridge l))
    (hq : 0 < μ.real (kstQuasiCrossing l k)) :
    1 - Real.sqrt (1 - μ.real (kstQuasiCrossing m l)) ≤
      max (μ.real (kstQuasiCrossing m k))
        ((1 - (1 - μ.real (kstBridge l)) ^ 2) /
          μ.real (kstQuasiCrossing l k)) := by
  let : IsProbabilityMeasure μ := hμ.1
  have hb := (kstBridge_isOpen l).measurableSet
  have hl := wired_kstTranslateEvent_probability θ μ hμ
    (-((l / 6 : ℕ) : ℤ), 0) hb
  have hr := wired_kstTranslateEvent_probability θ μ hμ
    (((l / 6 : ℕ) : ℤ), 0) hb
  have h := kst_cascade_of_kstCorridor μ
    (fun _ _ => wired_measurable_positive_association θ μ hμ)
    (kstQuasiCrossing_isOpen m k).measurableSet
    (kstAvoidingPath_isOpen l k).measurableSet
    (kstQuasiCrossing_isOpen l k).measurableSet
    (kstTranslateEvent_measurable _ hb) (kstTranslateEvent_measurable _ hb)
    (kstQuasiCrossing_isUpperSet m k) (kstAvoidingPath_isUpperSet l k)
    (kstQuasiCrossing_isUpperSet l k)
    (kstTranslateEvent_isUpperSet _ (kstBridge_isUpperSet l))
    (kstTranslateEvent_isUpperSet _ (kstBridge_isUpperSet l))
    (PlanarTopology.kst_quasi_partition m l k hml hlk hk)
    hcorridor (hr.trans hl.symm) hq
  simpa only [hl] using h

/-- Source closing relation with its deterministic gluing inclusion explicit. -/
theorem wired_kst_closing_of_kstCorridor (θ : Parameters)
    (μ : Measure LatticeConfiguration)
    (hμ : IsRCInfiniteVolumeLimit θ.toP θ.toQ 1 μ)
    (m l : ℕ)
    (hclosing : kstQuasiCrossing m l ∩ kstBridge l ⊆ kstBridge m) :
    μ.real (kstQuasiCrossing m l) * μ.real (kstBridge l) ≤ μ.real (kstBridge m) := by
  let : IsProbabilityMeasure μ := hμ.1
  exact kst_closing_of_kstCorridor μ
    (fun _ _ => wired_measurable_positive_association θ μ hμ)
    (kstQuasiCrossing_isOpen m l).measurableSet (kstBridge_isOpen l).measurableSet
    (kstQuasiCrossing_isUpperSet m l) (kstBridge_isUpperSet l) hclosing

/-- The wired closing relation with the geometry `PlanarTopology.kst_quasi_closing`
discharged. -/
theorem wired_kst_closing (θ : Parameters)
    (μ : Measure LatticeConfiguration)
    (hμ : IsRCInfiniteVolumeLimit θ.toP θ.toQ 1 μ)
    (m l : ℕ) (hml : l ≤ m) (hl : 1 ≤ l) :
    μ.real (kstQuasiCrossing m l) * μ.real (kstBridge l) ≤ μ.real (kstBridge m) :=
  wired_kst_closing_of_kstCorridor θ μ hμ m l
    (PlanarTopology.kst_quasi_closing m l hml hl)

end PottsContinuity.BD12
