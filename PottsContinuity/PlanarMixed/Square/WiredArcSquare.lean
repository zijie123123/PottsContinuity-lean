module

public import PottsContinuity.PlanarMixed.Square.WiredComparison
public import PottsContinuity.BD12.TwoBlockConnectivity
public import Mathlib.Tactic
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef

/-!
# The square mixed estimate in the actual WIRED-ARC direction, all q >= 1

The parameter is explicitly sqrt(q)/(1+sqrt(q)). No genuine-threshold
identification is asserted. Separate boundary classes enter only the FK law;
the crossing event requires actual sampled open edges between the two arcs.
-/

@[expose] public section

namespace PottsContinuity.PlanarMixed.Square
open PD.FK PD.Duality BD12
noncomputable section

/-- The wired-direction square estimate, in the sharper 1/(1+q) form. -/
theorem square_separateVertical_ge_inv_one_add_q
    (q : Set.Ici (1 : ℝ)) (z : ℤ) (N : ℕ) (hN : 1 ≤ N) :
    1 / (1 + (q:ℝ)) ≤
    (measure (rectangleGraph (z,z) N N) (criticalParameters q)
      (twoBlockBoundary (rectangleDoubleCollarInnerBottom (z,z) N N)
        (rectangleDoubleCollarInnerTop (z,z) N N)
        (rectangleDoubleCollarInnerBottom_disjoint_top (z,z) N N hN))
      (rectangleVerticalCrossingEvent (z,z) N N)).toReal := by
  have hsum := squareMixed_vertical_add_dualHorizontal_ge_one q z N hN
  have hbound := squareDualHorizontal_probability_le_q_mul_separateVertical
    (criticalParameters q) z N hN
  have hq : 1 ≤ (q:ℝ) := q.property
  have hden : 0 < 1+(q:ℝ) := by linarith only [hq]
  apply (div_le_iff₀ hden).mpr
  change _ ≤ (q:ℝ) * _ at hbound
  nlinarith only [hsum, hbound]

/-- The source's weaker constant, still in the actual wired direction. -/
theorem square_separateVertical_ge_inv_one_add_q_sq
    (q : Set.Ici (1 : ℝ)) (z : ℤ) (N : ℕ) (hN : 1 ≤ N) :
    1 / (1 + (q:ℝ)^2) ≤
    (measure (rectangleGraph (z,z) N N) (criticalParameters q)
      (twoBlockBoundary (rectangleDoubleCollarInnerBottom (z,z) N N)
        (rectangleDoubleCollarInnerTop (z,z) N N)
        (rectangleDoubleCollarInnerBottom_disjoint_top (z,z) N N hN))
      (rectangleVerticalCrossingEvent (z,z) N N)).toReal := by
  have hq : 1 ≤ (q:ℝ) := q.property
  have hden : 0 < 1+(q:ℝ) := by linarith only [hq]
  have hw : 1/(1+(q:ℝ)^2) ≤ 1/(1+(q:ℝ)) := by
    apply (div_le_div_iff₀ (by positivity) hden).mpr
    nlinarith only [hq, sq_nonneg ((q:ℝ)-1)]
  exact hw.trans (square_separateVertical_ge_inv_one_add_q q z N hN)

/-- The ordinary vertical crossing is exactly an actual path joining the
bottom and top vertex sets, including their corners. -/
theorem rectangleVerticalCrossing_eq_arcsConnection (a : LatticeVertex) (w h : ℕ) :
    rectangleVerticalCrossingEvent a w h =
      arcsConnectionEvent (rectangleGraph a w h)
        (rectangleDoubleCollarInnerBottom a w h) (rectangleDoubleCollarInnerTop a w h) := by
  ext C
  constructor
  · rintro ⟨u, v, hu, hv, hc⟩
    exact ⟨u, (Finset.mem_filter.mp hu).2, v, (Finset.mem_filter.mp hv).2, hc⟩
  · rintro ⟨u, hu, v, hv, hc⟩
    exact ⟨u, v, Finset.mem_filter.mpr ⟨u.property, hu⟩,
      Finset.mem_filter.mpr ⟨v.property, hv⟩, hc⟩

/-- Two opposite sides separately wired, the other two free: the wired arcs
are joined by an ACTUAL open path with probability at least 1/(1+q²). -/
theorem square_separate_wiredBottomTop_connection_lower
    (q : Set.Ici (1 : ℝ)) (z : ℤ) (N : ℕ) (hN : 1 ≤ N) :
    1 / (1 + (q:ℝ)^2) ≤
    (measure (rectangleGraph (z,z) N N) (criticalParameters q)
      (twoBlockBoundary (rectangleDoubleCollarInnerBottom (z,z) N N)
        (rectangleDoubleCollarInnerTop (z,z) N N)
        (rectangleDoubleCollarInnerBottom_disjoint_top (z,z) N N hN))
      (arcsConnectionEvent (rectangleGraph (z,z) N N)
        (rectangleDoubleCollarInnerBottom (z,z) N N)
        (rectangleDoubleCollarInnerTop (z,z) N N))).toReal := by
  rw [← rectangleVerticalCrossing_eq_arcsConnection]
  exact square_separateVertical_ge_inv_one_add_q_sq q z N hN

end
end PottsContinuity.PlanarMixed.Square
