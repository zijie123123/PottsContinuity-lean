module

public import PottsContinuity.Infinite.ClopenFKG
public import PottsContinuity.Infinite.MeasurableApprox

@[expose] public section

open MeasureTheory

namespace PottsContinuity.Infinite

open PottsContinuity
open PottsContinuity.PD.FK

noncomputable section

private theorem probabilityMeasure_fkg_of_clopen_ennreal
    (μ : Measure LatticeConfiguration) (hprob : IsProbabilityMeasure μ)
    (ν : ProbabilityMeasure LatticeConfiguration)
    (hν : (ν : Measure LatticeConfiguration) = μ)
    (hclopen : ∀ s t : Set LatticeConfiguration, IsClopen s → IsClopen t →
      IsUpperSet s → IsUpperSet t → μ s * μ t ≤ μ (s ∩ t))
    (s t : Set LatticeConfiguration) (hs : IsClopen s) (ht : IsClopen t)
    (hsu : IsUpperSet s) (htu : IsUpperSet t) :
    (((ν s : NNReal) : ℝ) * ((ν t : NNReal) : ℝ) ≤
      ((ν (s ∩ t) : NNReal) : ℝ)) := by
  let : IsProbabilityMeasure μ := hprob
  have h := hclopen s t hs ht hsu htu
  have hreal : μ.real s * μ.real t ≤ μ.real (s ∩ t) := by
    have h' := (ENNReal.toReal_le_toReal
      (ENNReal.mul_ne_top (measure_ne_top μ s) (measure_ne_top μ t))
      (measure_ne_top μ (s ∩ t))).2 h
    simpa [Measure.real_def, ENNReal.toReal_mul] using h'
  rw [← hν] at hreal
  simpa using hreal

private theorem ennreal_fkg_of_probabilityMeasure_fkg
    (μ : Measure LatticeConfiguration) (hprob : IsProbabilityMeasure μ)
    (ν : ProbabilityMeasure LatticeConfiguration)
    (hν : (ν : Measure LatticeConfiguration) = μ)
    {A B : Set LatticeConfiguration}
    (h : (((ν A : NNReal) : ℝ) * ((ν B : NNReal) : ℝ) ≤
      ((ν (A ∩ B) : NNReal) : ℝ))) :
    μ A * μ B ≤ μ (A ∩ B) := by
  let : IsProbabilityMeasure μ := hprob
  apply (ENNReal.toReal_le_toReal
    (ENNReal.mul_ne_top (measure_ne_top μ A) (measure_ne_top μ B))
    (measure_ne_top μ (A ∩ B))).1
  have h' : μ.real A * μ.real B ≤ μ.real (A ∩ B) := by
    have h'' : (ν : Measure LatticeConfiguration).real A *
        (ν : Measure LatticeConfiguration).real B ≤
        (ν : Measure LatticeConfiguration).real (A ∩ B) := by simpa using h
    rw [hν] at h''
    exact h''
  simpa [Measure.real_def, ENNReal.toReal_mul] using h'

/-- Infinite-volume FKG for measurable increasing events under the free limit. -/
theorem free_infinite_FKG_measurable
    (p : Set.Icc (0 : ℝ) 1) (q : Set.Ioi (0 : ℝ))
    (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1) (hq : 1 ≤ (q : ℝ))
    (μ : Measure (squareLattice.edgeSet → Bool))
    (hμ : IsRCInfiniteVolumeLimit p q 0 μ)
    (A B : Set LatticeConfiguration) (hA : MeasurableSet A)
    (hB : MeasurableSet B) (hAupper : IsUpperSet A) (hBupper : IsUpperSet B) :
    μ A * μ B ≤ μ (A ∩ B) := by
  let ν : ProbabilityMeasure LatticeConfiguration := ⟨μ, hμ.1⟩
  have hν : (ν : Measure LatticeConfiguration) = μ := rfl
  have hclopen : ∀ s t : Set LatticeConfiguration, IsClopen s → IsClopen t →
      IsUpperSet s → IsUpperSet t →
      (((ν s : NNReal) : ℝ) * ((ν t : NNReal) : ℝ) ≤
        ((ν (s ∩ t) : NNReal) : ℝ)) := by
    intro s t hs ht hsu htu
    exact probabilityMeasure_fkg_of_clopen_ennreal μ hμ.1 ν hν
      (fun s t hs ht hsu htu =>
        free_infinite_FKG_clopen p q hp0 hp1 hq μ hμ s t hs ht hsu htu)
      s t hs ht hsu htu
  have h := probabilityMeasure_measurable_upper_fkg_of_clopen ν hclopen hA hB hAupper hBupper
  exact ennreal_fkg_of_probabilityMeasure_fkg μ hμ.1 ν hν h

/-- Infinite-volume FKG for measurable increasing events under the wired limit. -/
theorem wired_infinite_FKG_measurable
    (p : Set.Icc (0 : ℝ) 1) (q : Set.Ioi (0 : ℝ))
    (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1) (hq : 1 ≤ (q : ℝ))
    (μ : Measure (squareLattice.edgeSet → Bool))
    (hμ : IsRCInfiniteVolumeLimit p q 1 μ)
    (A B : Set LatticeConfiguration) (hA : MeasurableSet A)
    (hB : MeasurableSet B) (hAupper : IsUpperSet A) (hBupper : IsUpperSet B) :
    μ A * μ B ≤ μ (A ∩ B) := by
  let ν : ProbabilityMeasure LatticeConfiguration := ⟨μ, hμ.1⟩
  have hν : (ν : Measure LatticeConfiguration) = μ := rfl
  have hclopen : ∀ s t : Set LatticeConfiguration, IsClopen s → IsClopen t →
      IsUpperSet s → IsUpperSet t →
      (((ν s : NNReal) : ℝ) * ((ν t : NNReal) : ℝ) ≤
        ((ν (s ∩ t) : NNReal) : ℝ)) := by
    intro s t hs ht hsu htu
    exact probabilityMeasure_fkg_of_clopen_ennreal μ hμ.1 ν hν
      (fun s t hs ht hsu htu =>
        wired_infinite_FKG_clopen p q hp0 hp1 hq μ hμ s t hs ht hsu htu)
      s t hs ht hsu htu
  have h := probabilityMeasure_measurable_upper_fkg_of_clopen ν hclopen hA hB hAupper hBupper
  exact ennreal_fkg_of_probabilityMeasure_fkg μ hμ.1 ν hν h

end
end PottsContinuity.Infinite
