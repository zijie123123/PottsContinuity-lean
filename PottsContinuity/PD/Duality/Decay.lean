-- Adapted from the author's PottsDiscontinuity formalization
-- (https://github.com/zijie123123/PottsDiscontinuity-lean), file `PottsDiscontinuity/Duality/Decay.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.PD.FK.BoxLaw
public import PottsContinuity.PD.Defs.RCInfiniteOpenGraph
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef

/-!
# Exponential two-point decay excludes an infinite origin cluster

The hypothesis below uses the integer lattice's ℓ¹ distance, explicitly
`|x₁| + |x₂|`. This module works for any measure with the stated bound; it
requires neither a Gibbs property nor planar duality. It does not prove wired
percolation or the discontinuity implication.
-/

@[expose] public section

open MeasureTheory

namespace PottsContinuity.PD.Duality

/-- The actual open cluster, with no boundary identifications. -/
def cluster (ω : FK.LatticeConfiguration) (v : ℤ × ℤ) : Set (ℤ × ℤ) :=
  {x | (rcInfiniteOpenGraph ω).Reachable v x}

/-- The two-point event for actual open connectivity. -/
def connectionEvent (v x : ℤ × ℤ) : Set FK.LatticeConfiguration :=
  {ω | x ∈ cluster ω v}

lemma summable_exp_neg_abs_int {c : ℝ} (hc : 0 < c) :
    Summable (fun n : ℤ => Real.exp (-c * |(n : ℝ)|)) := by
  apply summable_int_iff_summable_nat_and_neg.2
  have h := Real.summable_exp_nat_mul_iff.2 (neg_neg_of_pos hc)
  constructor
  · simpa only [Int.cast_natCast, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) _), mul_comm] using h
  · simpa only [Int.cast_neg, Int.cast_natCast, abs_neg,
      abs_of_nonneg (Nat.cast_nonneg (α := ℝ) _), mul_comm] using h

lemma summable_exp_neg_l1 {c : ℝ} (hc : 0 < c) :
    Summable (fun x : ℤ × ℤ => Real.exp (-c * (|(x.1 : ℝ)| + |(x.2 : ℝ)|))) := by
  have h := summable_exp_neg_abs_int hc
  have hh := h.mul_of_nonneg h (fun _ => (Real.exp_pos _).le)
    (fun _ => (Real.exp_pos _).le)
  simpa only [mul_add, Real.exp_add] using hh

/-- An explicit ℓ¹ exponential bound implies finite susceptibility. -/
theorem susceptibility_ne_top_of_exponential_decay
    (μ : Measure FK.LatticeConfiguration) (v : ℤ × ℤ)
    (C c : ℝ) (hc : 0 < c)
    (hdecay : ∀ x : ℤ × ℤ, μ (connectionEvent v x) ≤
      ENNReal.ofReal (C * Real.exp (-c * (|(x.1 : ℝ)| + |(x.2 : ℝ)|)))) :
    ∑' x : ℤ × ℤ, μ (connectionEvent v x) ≠ ⊤ := by
  have hs := ((summable_exp_neg_l1 hc).mul_left C).tsum_ofReal_ne_top
  exact ne_top_of_le_ne_top hs (ENNReal.tsum_le_tsum hdecay)

end PottsContinuity.PD.Duality
