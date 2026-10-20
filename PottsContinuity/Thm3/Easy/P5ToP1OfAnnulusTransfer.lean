module

public import PottsContinuity.Thm3.Easy.P5ToP5a
public import PottsContinuity.Thm3.Easy.P5OneArmPower
public import PottsContinuity.DualityExt.PositivePolygonRayIndex
public import PottsContinuity.Thm3.RSW.PolygonOuterBox

@[expose] public section

namespace PottsContinuity.Thm3.Easy

open MeasureTheory
open PottsContinuity
open PottsContinuity.PD.FK
open PottsContinuity.PD.RCInfinite
open PottsContinuity.DualityExt

/-- P5 implies wired nonpercolation once the P5a circuit bound transfers to
the wired-box annulus crossing complement at every dyadic scale. -/
theorem p5_implies_p1_of_annulusTransfer
    (q : Set.Ici (1 : ℝ))
    (μ : Measure (squareLattice.edgeSet → Bool))
    (hμ : IsRCInfiniteVolumeLimit
      (PottsContinuity.PD.FK.criticalParameters q).toP
      (PottsContinuity.PD.FK.criticalParameters q).toQ 1 μ)
    (hP5 : ∀ α : ℝ, 0 < α → ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 1 ≤ n →
      c ≤ rcEventProb
        (latticeRectangle (-(n : ℤ)) ⌊(α + 1) * (n : ℝ)⌋
          (-(n : ℤ)) (2 * (n : ℤ)))
        (criticalParameters q).toP (criticalParameters q).toQ 0
        (horizontalCrossing
          (latticeRectangle (-(n : ℤ)) ⌊(α + 1) * (n : ℝ)⌋
            (-(n : ℤ)) (2 * (n : ℤ)))
          0 ⌊α * (n : ℝ)⌋ 0 n))
    (hAnnulusTransfer : ∀ j : ℕ, 3 ≤ j →
      p5aAnnulusProbability (criticalParameters q) (2 ^ (j - 1) - 1) /
          (q : ℝ) ≤
        1 - (boxMeasure (criticalParameters q) 1 (0, 0) (2 ^ j) :
          Measure LatticeConfiguration).real
            {ω | annulusOpenCrossing (2 ^ (j - 1)) ω}) :
    μ {ω | {y | (PottsContinuity.rcInfiniteOpenGraph ω).Reachable
      (0, 0) y}.Infinite} = 0 := by
  obtain ⟨c₂, hc₂, hP5a⟩ := p5_implies_p5a q hP5
  have hqpos : 0 < (q : ℝ) := lt_of_lt_of_le (by norm_num) q.property
  let c : ℝ := min (c₂ / (q : ℝ)) (1 / 2)
  have hc : 0 < c := by
    dsimp [c]
    exact lt_min (div_pos hc₂ hqpos) (by norm_num)
  have hbound : ∀ j : ℕ, 3 ≤ j →
      (boxMeasure (criticalParameters q) 1 (0, 0) (2 ^ j) :
        Measure LatticeConfiguration).real
          {ω | annulusOpenCrossing (2 ^ (j - 1)) ω} ≤ 1 - c := by
    intro j hj
    have hjm : 2 ≤ j - 1 := by omega
    have hrad : 4 ≤ 2 ^ (j - 1) := by
      calc
        4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ (j - 1) := Nat.pow_le_pow_right (by norm_num) hjm
    have hscale : 2 ≤ 2 ^ (j - 1) - 1 := by omega
    have hP5aScale := hP5a (2 ^ (j - 1) - 1) hscale
    have hdiv : c₂ / (q : ℝ) ≤
        p5aAnnulusProbability (criticalParameters q) (2 ^ (j - 1) - 1) /
          (q : ℝ) :=
      div_le_div_of_nonneg_right hP5aScale (by positivity)
    have htransfer := hAnnulusTransfer j hj
    have hcprob : c ≤ 1 -
        (boxMeasure (criticalParameters q) 1 (0, 0) (2 ^ j) :
          Measure LatticeConfiguration).real
            {ω | annulusOpenCrossing (2 ^ (j - 1)) ω} := by
      dsimp [c]
      exact (min_le_left _ _).trans (hdiv.trans htransfer)
    linarith
  exact p5_implies_p1_of_annulusDuality q μ hμ ⟨c, hc, hbound⟩

end PottsContinuity.Thm3.Easy
