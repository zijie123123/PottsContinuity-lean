-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/HorizontalStripHeightLocalization.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.HorizontalStripLocalPathRestriction
public import PottsContinuity.FKC.FiniteFK.HorizontalStripHeightClopenApproximation
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.FKC.Medial

noncomputable section

open PottsContinuity.FKC.FiniteFK

/-- Two literal closed cuts within centered radius `M`, one strictly left of
column zero and one at or to its right. -/
def horizontalStripLocalClosedCutSuccess (M n : ℕ) : Set LatticeConfiguration :=
  {ω | ∃ l : ℤ, -(M : ℤ) ≤ l ∧ l < 0 ∧
      ∃ r : ℤ, 0 ≤ r ∧ r < (M : ℤ) ∧
        (∀ e ∈ horizontalStripCutEdges n l, ω e = false) ∧
        ∀ e ∈ horizontalStripCutEdges n r, ω e = false}

/-- If the origin's least top-connected height is at most `n`, two actual
closed cuts on opposite sides localize that connection into the actual finite
rectangle of radius `M`. -/
theorem horizontalStripHeightLE_and_localClosedCutSuccess_subset_finiteRectangle
    (M n : ℕ) :
    {ω | horizontalStripHeight n ω 0 ≤ n} ∩
      horizontalStripLocalClosedCutSuccess M n ⊆
        horizontalStripHeightFiniteRectangleEvent M n := by
  classical
  rintro ω ⟨hheight, hcuts⟩
  rcases hcuts with ⟨l, hlower, hleft, r, hright, hupper, hclosedL, hclosedR⟩
  obtain ⟨hh, hreach⟩ := horizontalStripHeight_spec n ω 0
  let u := horizontalStripVertexOfNat n 0 (horizontalStripHeight n ω 0) hh
  have hu : l < u.val.1 ∧ u.val.1 ≤ r := by
    constructor
    · change l < (0 : ℤ)
      exact hleft
    · change (0 : ℤ) ≤ r
      exact hright
  obtain ⟨v, hvTop, hvBound, p, hbound, q, hq⟩ :=
    horizontalStripTopReachable_lifts_to_rectangleRestriction_of_closed_cuts
      M n ω l r hclosedL hclosedR (by omega) (by omega) u hu hreach
  have hstartX :
      (horizontalStripRectangleVertexOfStrip M n u (by omega)).val.1 = 0 := by
    rw [horizontalStripRectangleVertexOfStrip_val]
    rfl
  have hstartY :
      (horizontalStripRectangleVertexOfStrip M n u (by omega)).val.2 ≤ (n : ℤ) := by
    rw [horizontalStripRectangleVertexOfStrip_val]
    change (horizontalStripHeight n ω 0 : ℤ) ≤ (n : ℤ)
    exact_mod_cast hheight
  refine ⟨horizontalStripRectangleVertexOfStrip M n u (by omega),
    horizontalStripRectangleVertexOfStrip M n v hvBound,
    hstartX, hstartY, ?_, ?_⟩
  · rw [horizontalStripRectangleVertexOfStrip_val]
    exact hvTop
  · exact ⟨q⟩

end
end PottsContinuity.FKC.Medial
