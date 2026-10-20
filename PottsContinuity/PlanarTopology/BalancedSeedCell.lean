module

public import PottsContinuity.PlanarTopology.RectangleSeedBalance
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

@[expose] public section

namespace PottsContinuity.PlanarTopology
open MeasureTheory PD.FK
noncomputable section

abbrev rectangleSeedLeftProbability (μ : Measure LatticeConfiguration) (W H s : ℕ)
    (v : Fin (W+1) × Fin (H+1)) : ℝ :=
  μ.real (rectangleSeedConnectionEvent W H s v {z | z.1 = 0})

abbrev rectangleSeedRightProbability (μ : Measure LatticeConfiguration) (W H s : ℕ)
    (v : Fin (W+1) × Fin (H+1)) : ℝ :=
  μ.real (rectangleSeedConnectionEvent W H s v {z | z.1 = ((W+s:ℕ):ℤ)})

abbrev rectangleSeedBottomProbability (μ : Measure LatticeConfiguration) (W H s : ℕ)
    (v : Fin (W+1) × Fin (H+1)) : ℝ :=
  μ.real (rectangleSeedConnectionEvent W H s v {z | z.2 = 0})

abbrev rectangleSeedTopProbability (μ : Measure LatticeConfiguration) (W H s : ℕ)
    (v : Fin (W+1) × Fin (H+1)) : ℝ :=
  μ.real (rectangleSeedConnectionEvent W H s v {z | z.2 = ((H+s:ℕ):ℤ)})

/-- Actual finite seed-probability comparisons at a common anchor v and two
reverse-comparison anchors x,y in the same unit cell. -/
structure RectangleSeedBalancedCell (μ : Measure LatticeConfiguration) (W H s : ℕ)
    (v x y : Fin (W+1) × Fin (H+1)) : Prop where
  left_ge_right : rectangleSeedRightProbability μ W H s v ≤ rectangleSeedLeftProbability μ W H s v
  bottom_ge_top : rectangleSeedTopProbability μ W H s v ≤ rectangleSeedBottomProbability μ W H s v
  right_ge_left : rectangleSeedLeftProbability μ W H s x ≤ rectangleSeedRightProbability μ W H s x
  top_ge_bottom : rectangleSeedBottomProbability μ W H s y ≤ rectangleSeedTopProbability μ W H s y
  right_close_fst : x.1.val ≤ v.1.val+1 ∧ v.1.val ≤ x.1.val+1
  right_close_snd : x.2.val ≤ v.2.val+1 ∧ v.2.val ≤ x.2.val+1
  top_close_fst : y.1.val ≤ v.1.val+1 ∧ v.1.val ≤ y.1.val+1
  top_close_snd : y.2.val ≤ v.2.val+1 ∧ v.2.val ≤ y.2.val+1

/-- A balanced seed cell exists for every probability measure and every
positive rectangle of admissible anchors; no probabilistic dependence premise. -/
theorem exists_rectangleSeedBalancedCell (μ : Measure LatticeConfiguration) [IsProbabilityMeasure μ]
    (W H s : ℕ) (hW : 0 < W) (hH : 0 < H) :
    ∃ v x y, RectangleSeedBalancedCell μ W H s v x y := by
  obtain ⟨v,hvL,hvB,x,hxR,hx₁,hx₂,y,hyT,hy₁,hy₂⟩ :=
    rectangle_seed_connection_balanced_cell μ W H s hW hH
  exact ⟨v,x,y,hvL,hvB,hxR,hyT,hx₁,hx₂,hy₁,hy₂⟩

end
end PottsContinuity.PlanarTopology
