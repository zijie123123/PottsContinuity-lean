-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/HorizontalStripLocalMinimumGeometry.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.HorizontalStripHeight

@[expose] public section

namespace PottsContinuity.FKC.Medial

/-- Any in-strip height connected to the top row is at least the least such height. -/
theorem horizontalStripHeight_le_of_topReachable
    (n : ℕ) (ω : LatticeConfiguration) (k : ℤ) (y : ℕ)
    (hy : y ≤ 2 * n)
    (hconn : horizontalStripTopReachable n ω (horizontalStripVertexOfNat n k y hy)) :
    horizontalStripHeight n ω k ≤ y := by
  classical
  exact Nat.find_min' (horizontalStripTopHeights_nonempty n ω k) (m := y) ⟨hy, hconn⟩

/-- A comparison of top-connection heights between two columns bounds the
height at the endpoint of an actual open strip path. -/
theorem horizontalStripHeight_le_of_local_minimum
    (n : ℕ) (ω : LatticeConfiguration) (k l : ℤ) (y : ℕ)
    (hk : horizontalStripHeight n ω k ≤ 2 * n)
    (hy : y ≤ 2 * n)
    (hlocal : horizontalStripHeight n ω k ≤ horizontalStripHeight n ω l)
    (hpath : (horizontalStripOpenGraph n ω).Reachable
      (horizontalStripVertexOfNat n k (horizontalStripHeight n ω k) hk)
      (horizontalStripVertexOfNat n l y hy)) :
    horizontalStripHeight n ω k ≤ y := by
  classical
  obtain ⟨_, htop⟩ := horizontalStripHeight_spec n ω k
  obtain ⟨x, htopPath⟩ := htop
  have hreach : horizontalStripTopReachable n ω
      (horizontalStripVertexOfNat n l y hy) := by
    exact ⟨x, hpath.symm.trans htopPath⟩
  exact le_trans hlocal (horizontalStripHeight_le_of_topReachable n ω l y hy hreach)

/-- The source local-minimum condition supplies the height comparison needed in
`horizontalStripHeight_le_of_local_minimum`. -/
theorem horizontalStripHeight_le_of_local_minimum_radius
    (n m : ℕ) (ω : LatticeConfiguration) (k l : ℤ) (y : ℕ)
    (hk : horizontalStripHeight n ω k ≤ 2 * n)
    (hy : y ≤ 2 * n)
    (hnear : (l - k).natAbs ≤ m)
    (hlocal : ∀ j : ℤ, (j - k).natAbs ≤ m →
      horizontalStripHeight n ω k ≤ horizontalStripHeight n ω j)
    (hpath : (horizontalStripOpenGraph n ω).Reachable
      (horizontalStripVertexOfNat n k (horizontalStripHeight n ω k) hk)
      (horizontalStripVertexOfNat n l y hy)) :
    horizontalStripHeight n ω k ≤ y := by
  exact horizontalStripHeight_le_of_local_minimum n ω k l y hk hy (hlocal l hnear) hpath

end PottsContinuity.FKC.Medial
