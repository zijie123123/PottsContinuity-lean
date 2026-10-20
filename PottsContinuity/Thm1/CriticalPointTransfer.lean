module

public import Mathlib
public import PottsContinuity.Frozen.Defs
public import PottsContinuity.BD12.CriticalValue

@[expose] public section

namespace PottsContinuity.Thm1

open MeasureTheory
open PottsContinuity

noncomputable section

/-- Random-cluster edge parameter corresponding to a nonnegative inverse temperature. -/
def pottsRCProbability (β : Set.Ici (0 : ℝ)) : Set.Icc (0 : ℝ) 1 :=
  ⟨1 - Real.exp (-(β : ℝ)), by
    constructor
    · have hβ : -(β : ℝ) ≤ 0 := neg_nonpos.mpr β.2
      have he : Real.exp (-(β : ℝ)) ≤ 1 := by
        simpa using Real.exp_le_exp.mpr hβ
      linarith
    · have he : 0 < Real.exp (-(β : ℝ)) := Real.exp_pos _
      linarith⟩

/-- The critical point transfer from the wired random-cluster magnetisation identity.
The hypotheses are the all-temperature Potts limit and the corrected infinite-volume
Edwards--Sokal identity for those limits. -/
theorem isPottsCriticalPoint_log_sqrt_of_limit_magnetisation
    (q : ℕ) (hq : 2 ≤ q)
    (hLimit : ∀ (β : Set.Ici (0 : ℝ)) (i : Fin q),
      ∃ μ : Measure (ℤ × ℤ → Fin q), IsPottsInfiniteVolumeLimit q β i μ)
    (hMag : ∀ (β : Set.Ici (0 : ℝ)) (i : Fin q)
      (μ : Measure (ℤ × ℤ → Fin q)), IsPottsInfiniteVolumeLimit q β i μ →
      ∀ ν : Measure (squareLattice.edgeSet → Bool),
        IsRCInfiniteVolumeLimit (pottsRCProbability β)
          ⟨(q : ℝ), Set.mem_Ioi.mpr (by exact_mod_cast (by omega : 0 < q))⟩ 1 ν →
        μ.real {σ | σ (0, 0) = i} =
          1 / (q : ℝ) + (1 - 1 / (q : ℝ)) *
            ν.real {ω | {y | (rcInfiniteOpenGraph ω).Reachable (0, 0) y}.Infinite}) :
    IsPottsCriticalPoint q (Real.log (1 + Real.sqrt (q : ℝ))) := by
  have hqpos : 0 < q := by omega
  have hqreal : 1 ≤ (q : ℝ) := by exact_mod_cast (by omega : 1 ≤ q)
  have hqrealpos : 0 < (q : ℝ) := lt_of_lt_of_le zero_lt_one hqreal
  let qReal : Set.Ici (1 : ℝ) := ⟨(q : ℝ), hqreal⟩
  let βc : ℝ := Real.log (1 + Real.sqrt (q : ℝ))
  have hsqrtpos : 0 < Real.sqrt (q : ℝ) := Real.sqrt_pos.2 hqrealpos
  have hβcpos : 0 < βc := by
    dsimp [βc]
    apply Real.log_pos
    linarith
  have hExp : Real.exp (-βc) = (1 + Real.sqrt (q : ℝ))⁻¹ := by
    dsimp [βc]
    rw [Real.exp_neg, Real.exp_log]
    positivity
  have hpcFormula :
      1 - Real.exp (-βc) =
        Real.sqrt (q : ℝ) / (1 + Real.sqrt (q : ℝ)) := by
    rw [hExp]
    have hden : (1 + Real.sqrt (q : ℝ)) ≠ 0 := by positivity
    field_simp
    ring
  have hpc : IsRCCriticalPoint qReal
      (Real.sqrt (q : ℝ) / (1 + Real.sqrt (q : ℝ))) :=
    BD12.isRCCriticalPoint_sqrt qReal
  refine ⟨hβcpos, ?_⟩
  intro β i
  obtain ⟨μ, hμ⟩ := hLimit β i
  obtain ⟨ν, hν, hbelow, habove⟩ := hpc.2 (pottsRCProbability β)
  have hidentity := hMag β i μ hμ ν hν
  refine ⟨μ, hμ, ?_, ?_⟩
  · intro hβ
    have hparam : (pottsRCProbability β : ℝ) <
        Real.sqrt (q : ℝ) / (1 + Real.sqrt (q : ℝ)) := by
      have hexp : Real.exp (-βc) < Real.exp (-(β : ℝ)) := by
        apply Real.exp_lt_exp.mpr
        dsimp [βc]
        linarith
      change 1 - Real.exp (-(β : ℝ)) < _
      linarith
    have hconn0 :
        ν.real {ω | {y | (rcInfiniteOpenGraph ω).Reachable (0, 0) y}.Infinite} = 0 := by
      simpa [Measure.real_def] using
        congrArg ENNReal.toReal (hbelow hparam)
    rw [hidentity, hconn0]
    ring
  · intro hβ
    have hparam :
        Real.sqrt (q : ℝ) / (1 + Real.sqrt (q : ℝ)) <
          (pottsRCProbability β : ℝ) := by
      have hexp : Real.exp (-(β : ℝ)) < Real.exp (-βc) := by
        apply Real.exp_lt_exp.mpr
        dsimp [βc]
        linarith
      change _ < 1 - Real.exp (-(β : ℝ))
      rw [← hpcFormula]
      linarith
    have hconn := habove hparam
    let : IsProbabilityMeasure ν := hν.1
    have hconnReal :
        0 < ν.real {ω | {y | (rcInfiniteOpenGraph ω).Reachable (0, 0) y}.Infinite} := by
      simpa [Measure.real_def] using
        ENNReal.toReal_pos hconn.ne' (measure_ne_top ν _)
    have hcoeff : 0 < 1 - 1 / (q : ℝ) := by
      have hqone : (1 : ℝ) < (q : ℝ) := by exact_mod_cast (by omega : 1 < q)
      rw [sub_pos]
      exact (div_lt_one hqrealpos).2 hqone
    rw [hidentity]
    have hmul := mul_pos hcoeff hconnReal
    nlinarith

end

end PottsContinuity.Thm1
