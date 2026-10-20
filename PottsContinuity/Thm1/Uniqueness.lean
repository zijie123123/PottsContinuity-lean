module

public import Mathlib
public import PottsContinuity.Frozen.Defs

@[expose] public section

open MeasureTheory Filter Topology

namespace PottsContinuity.Thm1

/-- Finite-coordinate cylinders on the Potts configuration space. -/
def pottsCylinder (q : ℕ) : Set (Set (ℤ × ℤ → Fin q)) :=
  {s | ∃ (A : Finset (ℤ × ℤ)) (ξ : ℤ × ℤ → Fin q),
    s = {σ | ∀ x ∈ A, σ x = ξ x}}

theorem pottsCylinder_measurable (q : ℕ) (A : Finset (ℤ × ℤ))
    (ξ : ℤ × ℤ → Fin q) :
    MeasurableSet {σ : ℤ × ℤ → Fin q | ∀ x ∈ A, σ x = ξ x} := by
  have hset : {σ : ℤ × ℤ → Fin q | ∀ x ∈ A, σ x = ξ x} =
      ⋂ x ∈ A, {σ | σ x = ξ x} := by
    ext σ
    simp
  rw [hset]
  exact Finset.measurableSet_biInter A
    (fun x _ => measurableSet_eq_fun (measurable_pi_apply x) measurable_const)

theorem pottsCylinder_isPiSystem (q : ℕ) : IsPiSystem (pottsCylinder q) := by
  rintro s ⟨A, ξ, rfl⟩ t ⟨B, ζ, rfl⟩ hne
  obtain ⟨ω, hωs, hωt⟩ := hne
  refine ⟨A ∪ B, ω, ?_⟩
  ext σ
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Finset.mem_union] at hωs hωt ⊢
  constructor
  · rintro ⟨hA, hB⟩ x (hx | hx)
    · rw [hA x hx, hωs x hx]
    · rw [hB x hx, hωt x hx]
  · intro h
    exact ⟨fun x hx => by rw [h x (Or.inl hx), hωs x hx],
      fun x hx => by rw [h x (Or.inr hx), hωt x hx]⟩

theorem pottsCylinder_generate (q : ℕ) :
    (MeasurableSpace.pi : MeasurableSpace (ℤ × ℤ → Fin q)) =
      MeasurableSpace.generateFrom (pottsCylinder q) := by
  apply le_antisymm
  · refine iSup_le fun a => ?_
    rintro s ⟨t, -, rfl⟩
    have hset : (fun b : ℤ × ℤ → Fin q => b a) ⁻¹' t =
        ⋃ c ∈ t, {σ | ∀ x ∈ ({a} : Finset (ℤ × ℤ)), σ x = (fun _ => c) x} := by
      ext σ
      simp
    rw [hset]
    refine MeasurableSet.biUnion (Set.to_countable t) (fun c _ => ?_)
    exact MeasurableSpace.measurableSet_generateFrom ⟨{a}, fun _ => c, rfl⟩
  · refine MeasurableSpace.generateFrom_le ?_
    rintro s ⟨A, ξ, rfl⟩
    exact pottsCylinder_measurable q A ξ

theorem measure_ext_pottsCylinder (q : ℕ) (μ ν : Measure (ℤ × ℤ → Fin q))
    [IsFiniteMeasure μ]
    (hc : ∀ (A : Finset (ℤ × ℤ)) (ξ : ℤ × ℤ → Fin q),
      μ {σ | ∀ x ∈ A, σ x = ξ x} = ν {σ | ∀ x ∈ A, σ x = ξ x})
    (hu : μ Set.univ = ν Set.univ) : μ = ν :=
  ext_of_generate_finite (pottsCylinder q) (pottsCylinder_generate q)
    (pottsCylinder_isPiSystem q)
    (by rintro s ⟨A, ξ, rfl⟩; exact hc A ξ) hu

def boxExhaustion (n : ℕ) : Finset (ℤ × ℤ) :=
  Finset.Icc (-(n : ℤ)) n ×ˢ Finset.Icc (-(n : ℤ)) n

private theorem boxExhaustion_mono : Monotone boxExhaustion := by
  intro m n h x hx
  simp only [boxExhaustion, Finset.mem_product, Finset.mem_Icc] at hx ⊢
  have hmn : (m : ℤ) ≤ n := by exact_mod_cast h
  omega

private theorem boxExhaustion_covers (x : ℤ × ℤ) :
    ∃ n, x ∈ boxExhaustion n := by
  refine ⟨x.1.natAbs + x.2.natAbs, ?_⟩
  simp only [boxExhaustion, Finset.mem_product, Finset.mem_Icc]
  omega

end PottsContinuity.Thm1

namespace PottsContinuity.Thm1

/-- The Potts infinite-volume limit is unique, for every `q`, `β`, and boundary colour. -/
theorem potts_limit_unique (q : ℕ) (β : ℝ) (i : Fin q)
    (μ ν : Measure (ℤ × ℤ → Fin q))
    (hμ : IsPottsInfiniteVolumeLimit q β i μ)
    (hν : IsPottsInfiniteVolumeLimit q β i ν) : μ = ν := by
  have hμfinite : IsFiniteMeasure μ := ⟨by
    rw [hμ.1.measure_univ]
    exact ENNReal.one_lt_top⟩
  refine @Thm1.measure_ext_pottsCylinder q μ ν hμfinite ?_ ?_
  · intro A ξ
    have hμlim := hμ.2 Thm1.boxExhaustion Thm1.boxExhaustion_mono
      Thm1.boxExhaustion_covers A ξ
    have hνlim := hν.2 Thm1.boxExhaustion Thm1.boxExhaustion_mono
      Thm1.boxExhaustion_covers A ξ
    have hreal : μ.real {σ | ∀ x ∈ A, σ x = ξ x} =
        ν.real {σ | ∀ x ∈ A, σ x = ξ x} := tendsto_nhds_unique hμlim hνlim
    have hμfinite' : μ {σ | ∀ x ∈ A, σ x = ξ x} ≠ ⊤ := ne_of_lt (calc
      μ {σ | ∀ x ∈ A, σ x = ξ x} ≤ μ Set.univ :=
        measure_mono (Set.subset_univ _)
      _ = 1 := hμ.1.measure_univ
      _ < ⊤ := ENNReal.one_lt_top)
    have hνfinite' : ν {σ | ∀ x ∈ A, σ x = ξ x} ≠ ⊤ := ne_of_lt (calc
      ν {σ | ∀ x ∈ A, σ x = ξ x} ≤ ν Set.univ :=
        measure_mono (Set.subset_univ _)
      _ = 1 := hν.1.measure_univ
      _ < ⊤ := ENNReal.one_lt_top)
    exact (ENNReal.toReal_eq_toReal_iff' hμfinite' hνfinite').mp hreal
  · simp [hμ.1.measure_univ, hν.1.measure_univ]

/-- The Potts critical inverse temperature is unique when `q ≥ 2`. -/
theorem potts_criticalPoint_unique (q : ℕ) (hq : 2 ≤ q) (βc βc' : ℝ)
    (h : IsPottsCriticalPoint q βc) (h' : IsPottsCriticalPoint q βc') :
    βc = βc' := by
  have hnot : ¬ βc < βc' := by
    intro hlt
    obtain ⟨_, hc⟩ := h
    obtain ⟨_, hc'⟩ := h'
    have hq0 : 0 < q := by omega
    let i : Fin q := ⟨0, hq0⟩
    let βm : ℝ := (βc + βc') / 2
    have hβm0 : 0 < βm := by dsimp [βm]; linarith
    obtain ⟨μ, hμ, _, hμgt⟩ := hc ⟨βm, le_of_lt hβm0⟩ i
    obtain ⟨ν, hν, hνeq, _⟩ := hc' ⟨βm, le_of_lt hβm0⟩ i
    have hμν := potts_limit_unique q βm i μ ν hμ hν
    have hmaggt : (1 / (q : ℝ)) < μ.real {σ | σ (0, 0) = i} :=
      hμgt (by dsimp [βm]; linarith)
    have hmageq : ν.real {σ | σ (0, 0) = i} = 1 / (q : ℝ) :=
      hνeq (by dsimp [βm]; linarith)
    rw [hμν] at hmaggt
    linarith
  have hnot' : ¬ βc' < βc := by
    intro hgt
    obtain ⟨_, hc⟩ := h
    obtain ⟨_, hc'⟩ := h'
    have hq0 : 0 < q := by omega
    let i : Fin q := ⟨0, hq0⟩
    let βm : ℝ := (βc' + βc) / 2
    have hβm0 : 0 < βm := by dsimp [βm]; linarith
    obtain ⟨μ, hμ, hμeq, _⟩ := hc ⟨βm, le_of_lt hβm0⟩ i
    obtain ⟨ν, hν, _, hνgt⟩ := hc' ⟨βm, le_of_lt hβm0⟩ i
    have hμν := potts_limit_unique q βm i μ ν hμ hν
    have hmageq : μ.real {σ | σ (0, 0) = i} = 1 / (q : ℝ) :=
      hμeq (by dsimp [βm]; linarith)
    have hmaggt : (1 / (q : ℝ)) < ν.real {σ | σ (0, 0) = i} :=
      hνgt (by dsimp [βm]; linarith)
    rw [← hμν] at hmaggt
    linarith
  rcases lt_trichotomy βc βc' with hlt | heq | hgt
  · exact (hnot hlt).elim
  · exact heq
  · exact (hnot' (by linarith : βc' < βc)).elim

end PottsContinuity.Thm1
