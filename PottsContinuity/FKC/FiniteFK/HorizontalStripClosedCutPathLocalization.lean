-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/HorizontalStripClosedCutPathLocalization.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.HorizontalStripCutGeometry

@[expose] public section

namespace PottsContinuity.FKC.Medial

/-- The inclusive vertex columns strictly to the right of cut `l` and at or
left of cut `r`. -/
def horizontalStripClosedCutColumnWindow (n : ℕ) (l r : ℤ) :
    Set (horizontalStripVertex n) :=
  {v | l < v.val.1 ∧ v.val.1 ≤ r}

/-- Every vertex in the support of a walk is reachable from its start by a
prefix of that walk. -/
private theorem horizontalStripWalk_start_reachable_of_mem_support
    (n : ℕ) (ω : LatticeConfiguration) {u v : horizontalStripVertex n}
    (p : (horizontalStripOpenGraph n ω).Walk u v) {z : horizontalStripVertex n}
    (hz : z ∈ p.support) : (horizontalStripOpenGraph n ω).Reachable u z := by
  induction p with
  | nil =>
      simp only [SimpleGraph.Walk.support_nil, List.mem_singleton] at hz
      subst z
      exact SimpleGraph.Reachable.refl _
  | @cons a b c hadj p ih =>
      simp only [SimpleGraph.Walk.support_cons, List.mem_cons] at hz
      rcases hz with rfl | hz
      · exact SimpleGraph.Reachable.refl _
      · exact hadj.reachable.trans (ih hz)

/-- A path from right of a closed cut cannot visit its left side. -/
private theorem horizontalStripClosedCut_reachable_gt
    (n : ℕ) (ω : LatticeConfiguration) (k : ℤ)
    {u v : horizontalStripVertex n} (hclosed :
      ∀ e ∈ horizontalStripCutEdges n k, ω e = false)
    (hu : k < u.val.1) (hconn : (horizontalStripOpenGraph n ω).Reachable u v) :
    k < v.val.1 := by
  by_contra hv
  have hv' : v.val.1 ≤ k := by omega
  have hnot := horizontalStripClosedCut_not_reachable n ω k v u hv' hu
  exact hnot hclosed hconn.symm

/-- A path from at or left of a closed cut cannot visit its right side. -/
private theorem horizontalStripClosedCut_reachable_le
    (n : ℕ) (ω : LatticeConfiguration) (k : ℤ)
    {u v : horizontalStripVertex n} (hclosed :
      ∀ e ∈ horizontalStripCutEdges n k, ω e = false)
    (hu : u.val.1 ≤ k) (hconn : (horizontalStripOpenGraph n ω).Reachable u v) :
    v.val.1 ≤ k := by
  by_contra hv
  have hv' : k < v.val.1 := by omega
  have hnot := horizontalStripClosedCut_not_reachable n ω k u v hu hv' hclosed
  exact hnot hconn

/-- Every vertex visited by a strip-open walk started between two closed cuts
stays in the literal interval between them. -/
theorem horizontalStripWalk_support_localized_by_closed_cuts
    (n : ℕ) (ω : LatticeConfiguration) (l r : ℤ)
    (hclosedL : ∀ e ∈ horizontalStripCutEdges n l, ω e = false)
    (hclosedR : ∀ e ∈ horizontalStripCutEdges n r, ω e = false)
    {u v : horizontalStripVertex n}
    (p : (horizontalStripOpenGraph n ω).Walk u v)
    (hu : l < u.val.1 ∧ u.val.1 ≤ r) :
    ∀ z ∈ p.support, z ∈ horizontalStripClosedCutColumnWindow n l r := by
  intro z hz
  have hreach := horizontalStripWalk_start_reachable_of_mem_support n ω p hz
  change l < z.val.1 ∧ z.val.1 ≤ r
  constructor
  · exact horizontalStripClosedCut_reachable_gt n ω l hclosedL hu.1 hreach
  · exact horizontalStripClosedCut_reachable_le n ω r hclosedR hu.2 hreach

end PottsContinuity.FKC.Medial
