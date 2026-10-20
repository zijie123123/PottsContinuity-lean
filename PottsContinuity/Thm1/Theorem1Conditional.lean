module

public import Mathlib
public import PottsContinuity.Thm1.CriticalPointTransfer
public import PottsContinuity.WellDefined.Uniqueness

@[expose] public section

namespace PottsContinuity.Thm1

open MeasureTheory
open PottsContinuity

noncomputable section

/-- Theorem 1 assembled from the exact Theorem 2 conclusion, conditional on
the all-temperature Potts limits and their corrected magnetisation identity. -/
theorem theorem_1_of_theorem2_of_limit_magnetisation
    (hLimit : ∀ (q : ℕ) (β : Set.Ici (0 : ℝ)) (i : Fin q),
      ∃ μ : Measure (ℤ × ℤ → Fin q), IsPottsInfiniteVolumeLimit q β i μ)
    (hMag : ∀ (q : ℕ) (hq : 1 ≤ q) (β : Set.Ici (0 : ℝ)) (i : Fin q)
      (μ : Measure (ℤ × ℤ → Fin q)), IsPottsInfiniteVolumeLimit q β i μ →
      ∀ ν : Measure (squareLattice.edgeSet → Bool),
        IsRCInfiniteVolumeLimit (pottsRCProbability β)
          ⟨(q : ℝ), Set.mem_Ioi.mpr (by exact_mod_cast (by omega : 0 < q))⟩ 1 ν →
        μ.real {σ | σ (0, 0) = i} =
          1 / (q : ℝ) + (1 - 1 / (q : ℝ)) *
            ν.real {ω | {y | (rcInfiniteOpenGraph ω).Reachable (0, 0) y}.Infinite})
    (hTheorem2 : ∀ (q : ℝ) (hq : q ∈ Set.Icc (1 : ℝ) 4),
      ∃ (pc : Set.Icc (0 : ℝ) 1) (φ₁ : Measure (squareLattice.edgeSet → Bool)),
        IsRCCriticalPoint ⟨q, hq.1⟩ pc ∧
        IsRCInfiniteVolumeLimit pc ⟨q, lt_of_lt_of_le one_pos hq.1⟩ 1 φ₁ ∧
        φ₁ {ω | {y | (rcInfiniteOpenGraph ω).Reachable (0, 0) y}.Infinite} = 0)
    (q : ℕ) (hq : q ∈ Set.Icc 2 4) :
    ∃ βc : ℝ, IsPottsCriticalPoint q βc ∧
      ∀ i : Fin q, ∃ μ : Measure (ℤ × ℤ → Fin q),
        IsPottsInfiniteVolumeLimit q βc i μ ∧
          μ.real {σ | σ (0, 0) = i} = 1 / (q : ℝ) := by
  have hq2 : 2 ≤ q := hq.1
  have hqreal : (q : ℝ) ∈ Set.Icc (1 : ℝ) 4 := by
    constructor
    · exact_mod_cast (show 1 ≤ q by omega)
    · exact_mod_cast hq.2
  let qReal : Set.Ici (1 : ℝ) := ⟨(q : ℝ), hqreal.1⟩
  have hLimitQ : ∀ (β : Set.Ici (0 : ℝ)) (i : Fin q),
      ∃ μ : Measure (ℤ × ℤ → Fin q), IsPottsInfiniteVolumeLimit q β i μ := by
    intro β i
    exact hLimit q β i
  have hMagQ : ∀ (β : Set.Ici (0 : ℝ)) (i : Fin q)
      (μ : Measure (ℤ × ℤ → Fin q)), IsPottsInfiniteVolumeLimit q β i μ →
      ∀ ν : Measure (squareLattice.edgeSet → Bool),
        IsRCInfiniteVolumeLimit (pottsRCProbability β)
          ⟨(q : ℝ), Set.mem_Ioi.mpr (by exact_mod_cast (by omega : 0 < q))⟩ 1 ν →
        μ.real {σ | σ (0, 0) = i} =
          1 / (q : ℝ) + (1 - 1 / (q : ℝ)) *
            ν.real {ω | {y | (rcInfiniteOpenGraph ω).Reachable (0, 0) y}.Infinite} := by
    intro β i μ hμ ν hν
    exact hMag q (by omega) β i μ hμ ν hν
  have hCritical := isPottsCriticalPoint_log_sqrt_of_limit_magnetisation
    q hq2 hLimitQ hMagQ
  let βc : ℝ := Real.log (1 + Real.sqrt (q : ℝ))
  let βcArg : Set.Ici (0 : ℝ) := ⟨βc, hCritical.1.le⟩
  obtain ⟨pc, φ₁, hpc, hφ₁, hzero⟩ := hTheorem2 (q : ℝ) hqreal
  have hpcValue : (pc : ℝ) = Real.sqrt (q : ℝ) / (1 + Real.sqrt (q : ℝ)) := by
    exact BD12.genuine_criticalPoint_eq_sqrt qReal (pc : ℝ) (by simpa [qReal] using hpc)
  have hβexp : Real.exp (-βc) = (1 + Real.sqrt (q : ℝ))⁻¹ := by
    dsimp [βc]
    rw [Real.exp_neg, Real.exp_log]
    positivity
  have hβParameter :
      (pottsRCProbability βcArg : ℝ) = Real.sqrt (q : ℝ) / (1 + Real.sqrt (q : ℝ)) := by
    change 1 - Real.exp (-βc) = _
    rw [hβexp]
    have hden : (1 + Real.sqrt (q : ℝ)) ≠ 0 := by positivity
    field_simp
    ring
  have hpEq : pottsRCProbability βcArg = pc := by
    apply Subtype.ext
    rw [hβParameter, hpcValue]
  have hCriticalRC := BD12.isRCCriticalPoint_sqrt qReal
  obtain ⟨ν, hν, _, _⟩ := hCriticalRC.2 (pottsRCProbability βcArg)
  have hφ₁' : IsRCInfiniteVolumeLimit (pottsRCProbability βcArg)
      ⟨(q : ℝ), Set.mem_Ioi.mpr (by exact_mod_cast (by omega : 0 < q))⟩ 1 φ₁ := by
    rw [← hpEq] at hφ₁
    simpa [qReal] using hφ₁
  have hνφ : ν = φ₁ := WellDefined.limit_unique (pottsRCProbability βcArg)
    ⟨(q : ℝ), Set.mem_Ioi.mpr (by exact_mod_cast (by omega : 0 < q))⟩ 1 ν φ₁
      (by simpa [qReal] using hν) hφ₁'
  refine ⟨βc, hCritical, ?_⟩
  intro i
  obtain ⟨μ, hμ⟩ := hLimit q βcArg i
  have hidentity := hMagQ βcArg i μ hμ ν (by simpa [qReal] using hν)
  have hzeroReal :
      ν.real {ω | {y | (rcInfiniteOpenGraph ω).Reachable (0, 0) y}.Infinite} = 0 := by
    have hmass := congrArg (fun ρ : Measure (squareLattice.edgeSet → Bool) =>
      ρ {ω | {y | (rcInfiniteOpenGraph ω).Reachable (0, 0) y}.Infinite}) hνφ
    simpa [Measure.real_def] using congrArg ENNReal.toReal (hmass.trans hzero)
  refine ⟨μ, hμ, ?_⟩
  rw [hidentity, hzeroReal]
  ring

end

end PottsContinuity.Thm1
