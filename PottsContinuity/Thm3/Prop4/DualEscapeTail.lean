module

public import PottsContinuity.Thm3.Prop4.SquareEscape
public import PottsContinuity.Thm3.Prop4.StretchedSummability

/-!
# Corrected stretched-exponential bounds for actual dual escapes

The c₀ coefficient is retained. Real square-radius thresholds use ceilings,
and the whole-plane bound is uniform in the dual face root. Finite candidate
unions and their vanishing errors require no independence between the arms.
-/

@[expose] public section

open MeasureTheory Filter Topology

namespace PottsContinuity.Thm3.Prop4

open PD.FK.Medial

/-- The true closed-dual escape estimate, with exact real-radius rounding. -/
theorem selfDual_wired_dual_square_escape_le_stretched (q : Set.Ici (1 : ℝ))
    (μ₀ μ₁ : Measure PD.FK.LatticeConfiguration)
    (hμ₀ : IsRCInfiniteVolumeLimit (RSW.selfDualParameters q).toP
      (RSW.selfDualParameters q).toQ 0 μ₀)
    (hμ₁ : IsRCInfiniteVolumeLimit (RSW.selfDualParameters q).toP
      (RSW.selfDualParameters q).toQ 1 μ₁)
    (c₀ α : ℝ) (hc₀ : 0 < c₀) (hα : 0 < α)
    (hdecay : ∀ n : ℕ, 1 ≤ n → RSW.oneArmProbability μ₀ n ≤ Real.exp (-c₀*(n : ℝ)^α))
    (x : ℤ × ℤ) (r : ℝ) (hr : 1 ≤ r) :
    μ₁.real {ω | ∃ z : ℤ × ℤ, r ≤ (max |z.1-x.1| |z.2-x.2| : ℤ) ∧
      (wholePlaneClosedDualGraph ω).Reachable x z} ≤ Real.exp (-c₀*r^α) := by
  have hr0 : 0 ≤ r := by linarith only [hr]
  rw [selfDual_wired_dual_square_escape_probability q μ₀ μ₁ hμ₀ hμ₁ x r hr0]
  have hn : 1 ≤ ⌈r⌉₊ := by
    have hpos := Nat.ceil_pos.mpr (by linarith only [hr] : 0 < r)
    omega
  apply (hdecay ⌈r⌉₊ hn).trans
  apply Real.exp_le_exp.mpr
  have hpow := Real.rpow_le_rpow hr0 (Nat.le_ceil r) hα.le
  nlinarith only [hpow,hc₀]

/-- A finite set of candidate dual roots costs its cardinality, not a terminal-vertex sum. -/
theorem selfDual_wired_dual_square_escape_union_le (q : Set.Ici (1 : ℝ))
    (μ₀ μ₁ : Measure PD.FK.LatticeConfiguration)
    (hμ₀ : IsRCInfiniteVolumeLimit (RSW.selfDualParameters q).toP
      (RSW.selfDualParameters q).toQ 0 μ₀)
    (hμ₁ : IsRCInfiniteVolumeLimit (RSW.selfDualParameters q).toP
      (RSW.selfDualParameters q).toQ 1 μ₁)
    (c₀ α : ℝ) (hc₀ : 0 < c₀) (hα : 0 < α)
    (hdecay : ∀ n : ℕ, 1 ≤ n → RSW.oneArmProbability μ₀ n ≤ Real.exp (-c₀*(n : ℝ)^α))
    (F : Finset (ℤ × ℤ)) (r : ℝ) (hr : 1 ≤ r) :
    μ₁.real {ω | ∃ x ∈ F, ∃ z : ℤ × ℤ, r ≤ (max |z.1-x.1| |z.2-x.2| : ℤ) ∧
      (wholePlaneClosedDualGraph ω).Reachable x z} ≤ (F.card : ℝ)*Real.exp (-c₀*r^α) := by
  let : IsProbabilityMeasure μ₁ := hμ₁.1
  have heq : {ω : PD.FK.LatticeConfiguration | ∃ x ∈ F, ∃ z : ℤ × ℤ,
      r ≤ (max |z.1-x.1| |z.2-x.2| : ℤ) ∧ (wholePlaneClosedDualGraph ω).Reachable x z} =
      ⋃ x ∈ F, {ω | ∃ z : ℤ × ℤ, r ≤ (max |z.1-x.1| |z.2-x.2| : ℤ) ∧
        (wholePlaneClosedDualGraph ω).Reachable x z} := by
    ext ω
    simp only [Set.mem_iUnion,Set.mem_ofPred_eq,exists_prop]
  rw [heq]
  apply (measureReal_biUnion_finset_le F _).trans
  calc
    _ ≤ ∑ _x ∈ F, Real.exp (-c₀*r^α) := Finset.sum_le_sum (fun x _ =>
      selfDual_wired_dual_square_escape_le_stretched q μ₀ μ₁ hμ₀ hμ₁ c₀ α hc₀ hα hdecay x r hr)
    _ = _ := by simp

end PottsContinuity.Thm3.Prop4
