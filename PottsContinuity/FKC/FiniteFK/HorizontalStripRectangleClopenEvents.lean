-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/HorizontalStripRectangleClopenEvents.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.HorizontalStripRectangleLaw
public import PottsContinuity.FKC.FiniteFK.HorizontalStripRectangleConfiguration
public import PottsContinuity.FKC.FiniteFK.DisjointPatternAvoidance
public import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
public import Mathlib.Algebra.Order.Field.Basic
public import PottsContinuity.FKC.FiniteFK.RectangleEvents
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.MeasureTheory.Measure.Portmanteau
public import Mathlib.Tactic

@[expose] public section

open MeasureTheory Filter Topology

namespace PottsContinuity.FKC.Medial

noncomputable section

local instance horizontalClopenEdgeFintype (M n : ℕ) :
    Fintype (horizontalStripCutRectangle M n).edgeSet := Fintype.ofFinite _
local instance horizontalClopenEdgeDecidableEq (M n : ℕ) :
    DecidableEq (horizontalStripCutRectangle M n).edgeSet := Classical.decEq _

/-- Restrict any whole-plane state to the literal finite rectangle edge set. -/
def horizontalStripRectangleRestriction (M n : ℕ) (ω : LatticeConfiguration) :
    PottsContinuity.FKC.FiniteFK.Configuration (horizontalStripCutRectangle M n) := by
  classical
  exact Finset.univ.filter (fun e =>
    ω (horizontalStripRectangleOriginalEdge M n e) = true)

@[simp] theorem horizontalStripRectangleRestriction_mem (M n : ℕ)
    (ω : LatticeConfiguration) (e : (horizontalStripCutRectangle M n).edgeSet) :
    e ∈ horizontalStripRectangleRestriction M n ω ↔
      ω (horizontalStripRectangleOriginalEdge M n e) = true := by
  simp [horizontalStripRectangleRestriction]

private theorem horizontalStripRectangleOriginalEdge_eq_of_adj
    (M n : ℕ) {u v : RectangleVertex (-(M : ℤ), 0) (2 * M) (2 * n)}
    (h : (horizontalStripCutRectangle M n).Adj u v) :
    horizontalStripRectangleOriginalEdge M n ⟨s(u, v), h⟩ =
      ⟨s(u.val, v.val), (squareLattice.mem_edgeSet).mpr
        ((rectangleGraph_adj_iff (-(M : ℤ), 0) (2 * M) (2 * n) u v).mp h)⟩ := by
  apply Subtype.ext
  apply Sym2.eq_iff.mpr
  exact Or.inl ⟨rfl, rfl⟩

/-- Every whole-plane state, not just a closed extension, restricts to the
finite open graph determined by its original rectangle-edge coordinates. -/
theorem horizontalStripRectangleOpenGraph_eq_openGraph_restriction
    (M n : ℕ) (ω : LatticeConfiguration) :
    horizontalStripRectangleOpenGraph M n ω =
      PottsContinuity.FKC.FiniteFK.openGraph (horizontalStripCutRectangle M n)
        (horizontalStripRectangleRestriction M n ω) := by
  classical
  ext u v
  rw [PottsContinuity.FKC.FiniteFK.openGraph_adj]
  change (∃ h : squareLattice.Adj u.val v.val,
      ω ⟨s(u.val, v.val), squareLattice.mem_edgeSet.mpr h⟩ = true) ↔
    s(u, v) ∈ PottsContinuity.FKC.FiniteFK.openEdges (horizontalStripCutRectangle M n)
      (horizontalStripRectangleRestriction M n ω)
  constructor
  · rintro ⟨hsq, hopen⟩
    have hadj : (horizontalStripCutRectangle M n).Adj u v :=
      (rectangleGraph_adj_iff _ _ _ _ _).2 hsq
    let e : (horizontalStripCutRectangle M n).edgeSet := ⟨s(u, v), hadj⟩
    have heq : horizontalStripRectangleOriginalEdge M n e =
        ⟨s(u.val, v.val), squareLattice.mem_edgeSet.mpr hsq⟩ :=
      horizontalStripRectangleOriginalEdge_eq_of_adj M n hadj
    have he : e ∈ horizontalStripRectangleRestriction M n ω := by
      apply (horizontalStripRectangleRestriction_mem M n ω e).2
      simpa [heq] using hopen
    change s(u, v) ∈ Subtype.val ''
      (↑(horizontalStripRectangleRestriction M n ω) : Set (horizontalStripCutRectangle M n).edgeSet)
    exact ⟨e, he, rfl⟩
  · intro hmem
    change s(u, v) ∈ Subtype.val ''
      (↑(horizontalStripRectangleRestriction M n ω) : Set (horizontalStripCutRectangle M n).edgeSet) at hmem
    rcases hmem with ⟨e, he, hval⟩
    have hadj : (horizontalStripCutRectangle M n).Adj u v := by
      apply (horizontalStripCutRectangle M n).mem_edgeSet.mp
      rw [← hval]
      exact e.property
    have hsq : squareLattice.Adj u.val v.val :=
      (rectangleGraph_adj_iff _ _ _ _ _).mp hadj
    have heEq : e = (⟨s(u, v), hadj⟩ : (horizontalStripCutRectangle M n).edgeSet) := by
      apply Subtype.ext
      exact hval
    have hopen : ω (⟨s(u.val, v.val), squareLattice.mem_edgeSet.mpr hsq⟩ : squareLattice.edgeSet) = true := by
      have hr := (horizontalStripRectangleRestriction_mem M n ω e).mp he
      rw [heEq, horizontalStripRectangleOriginalEdge_eq_of_adj M n hadj] at hr
      exact hr
    exact ⟨hsq, hopen⟩

end
end PottsContinuity.FKC.Medial

