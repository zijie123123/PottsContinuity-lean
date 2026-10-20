-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/HorizontalStripHeightFiniteExhaustion.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.HorizontalStripLocalPathRestriction
public import PottsContinuity.FKC.FiniteFK.HorizontalStripHeightClopenApproximation
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.FKC.Medial

noncomputable section

open PottsContinuity.FKC.FiniteFK

/-- The origin-column least-height event is the increasing union of the
actual finite-rectangle events, since every witnessing strip walk has finite
support and hence lies in some centered rectangle. -/
theorem horizontalStripHeightLE_eq_iUnion_finiteRectangleEvent (n : ℕ) :
    {ω | horizontalStripHeight n ω 0 ≤ n} =
      ⋃ M : ℕ, horizontalStripHeightFiniteRectangleEvent M n := by
  classical
  ext ω
  constructor
  · intro hheight
    obtain ⟨hh, hreach⟩ := horizontalStripHeight_spec n ω 0
    let u := horizontalStripVertexOfNat n 0 (horizontalStripHeight n ω 0) hh
    obtain ⟨x, hconn⟩ := hreach
    obtain ⟨p⟩ := hconn
    let S : Finset ℕ := p.support.toFinset.image fun z => z.val.1.natAbs
    let M : ℕ := S.sup (fun x : ℕ => x)
    have hbound : ∀ z ∈ p.support,
        -(M : ℤ) ≤ z.val.1 ∧ z.val.1 ≤ M := by
      intro z hz
      have hmem : z.val.1.natAbs ∈ S := by
        apply Finset.mem_image.mpr
        refine ⟨z, ?_, rfl⟩
        simpa using hz
      have habs : z.val.1.natAbs ≤ M := by
        dsimp [M]
        exact Finset.le_sup (s := S) (f := fun x : ℕ => x) hmem
      have hcast : ((z.val.1).natAbs : ℤ) = |z.val.1| := by
        exact Int.natCast_natAbs _
      have habs' : |z.val.1| ≤ (M : ℤ) := by
        rw [← hcast]
        exact_mod_cast habs
      exact abs_le.mp habs'
    have hlift := horizontalStripWalk_lifts_to_rectangleRestriction M n ω p hbound
    let v := horizontalStripVertexOfNat n x (2 * n) (le_rfl)
    have hstartX :
        (horizontalStripRectangleVertexOfStrip M n u (hbound u p.start_mem_support)).val.1 = 0 := by
      rw [horizontalStripRectangleVertexOfStrip_val]
      rfl
    have hstartY :
        (horizontalStripRectangleVertexOfStrip M n u (hbound u p.start_mem_support)).val.2 ≤ (n : ℤ) := by
      rw [horizontalStripRectangleVertexOfStrip_val]
      change (horizontalStripHeight n ω 0 : ℤ) ≤ (n : ℤ)
      exact_mod_cast hheight
    have hendY :
        (horizontalStripRectangleVertexOfStrip M n v (hbound v p.end_mem_support)).val.2 =
          (2 * n : ℤ) := by
      rw [horizontalStripRectangleVertexOfStrip_val]
      rfl
    obtain ⟨q, hq⟩ := hlift
    apply Set.mem_iUnion.mpr
    refine ⟨M, ?_⟩
    refine ⟨horizontalStripRectangleVertexOfStrip M n u (hbound u p.start_mem_support),
      horizontalStripRectangleVertexOfStrip M n v (hbound v p.end_mem_support),
      hstartX, hstartY, hendY, ?_⟩
    exact ⟨q⟩
  · intro hω
    obtain ⟨M, hM⟩ := Set.mem_iUnion.mp hω
    exact horizontalStripHeightFiniteRectangleEvent_subset_heightLE M n hM

end
end PottsContinuity.FKC.Medial
