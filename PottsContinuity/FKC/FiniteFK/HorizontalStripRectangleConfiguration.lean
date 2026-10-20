-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/HorizontalStripRectangleConfiguration.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.HorizontalStripCutRectangle
public import PottsContinuity.FKC.FiniteFK.Graph

@[expose] public section

namespace PottsContinuity.FKC.Medial

open PottsContinuity.FKC

noncomputable section

/-- Extend a finite rectangle configuration by closing every original edge
outside its embedded edge set. -/
def horizontalStripRectanglePlaneExtension (M n : ℕ)
    (A : Finset (horizontalStripCutRectangle M n).edgeSet) : LatticeConfiguration := by
  classical
  exact fun e => decide (e ∈ A.image (horizontalStripRectangleOriginalEdge M n))

@[simp] theorem horizontalStripRectanglePlaneExtension_mem_originalEdge
    (M n : ℕ) (A : Finset (horizontalStripCutRectangle M n).edgeSet)
    (e : (horizontalStripCutRectangle M n).edgeSet) :
    horizontalStripRectanglePlaneExtension M n A (horizontalStripRectangleOriginalEdge M n e) = true ↔
      e ∈ A := by
  classical
  constructor
  · intro h
    have hmem : horizontalStripRectangleOriginalEdge M n e ∈
        A.image (horizontalStripRectangleOriginalEdge M n) := of_decide_eq_true h
    rcases Finset.mem_image.mp hmem with ⟨e', he', heq⟩
    have he'' : e' = e := horizontalStripRectangleOriginalEdge_injective M n heq
    simpa [he''] using he'
  · intro he
    have hm : horizontalStripRectangleOriginalEdge M n e ∈
        A.image (horizontalStripRectangleOriginalEdge M n) :=
      Finset.mem_image.mpr ⟨e, he, rfl⟩
    change decide (horizontalStripRectangleOriginalEdge M n e ∈
      A.image (horizontalStripRectangleOriginalEdge M n)) = true
    simp [hm]

@[simp] theorem horizontalStripRectanglePlaneExtension_false_of_not_mem_image
    (M n : ℕ) (A : Finset (horizontalStripCutRectangle M n).edgeSet)
    (e : squareLattice.edgeSet)
    (he : e ∉ A.image (horizontalStripRectangleOriginalEdge M n)) :
    horizontalStripRectanglePlaneExtension M n A e = false := by
  simp [horizontalStripRectanglePlaneExtension, he]

private theorem horizontalStripRectangleOriginalEdge_eq_of_adj
    (M n : ℕ) {u v : RectangleVertex (-(M : ℤ), 0) (2 * M) (2 * n)}
    (h : (horizontalStripCutRectangle M n).Adj u v) :
    horizontalStripRectangleOriginalEdge M n ⟨s(u, v), h⟩ =
      ⟨s(u.val, v.val), (squareLattice.mem_edgeSet).mpr
        ((rectangleGraph_adj_iff (-(M : ℤ), 0) (2 * M) (2 * n) u v).mp h)⟩ := by
  apply Subtype.ext
  apply Sym2.eq_iff.mpr
  exact Or.inl ⟨rfl, rfl⟩

private theorem horizontalStripRectangleOpenGraph_adj_iff
    (M n : ℕ) (A : Finset (horizontalStripCutRectangle M n).edgeSet)
    (u v : RectangleVertex (-(M : ℤ), 0) (2 * M) (2 * n)) :
    (horizontalStripRectangleOpenGraph M n
      (horizontalStripRectanglePlaneExtension M n A)).Adj u v ↔
    (FiniteFK.openGraph (horizontalStripCutRectangle M n) A).Adj u v := by
  constructor
  · rintro ⟨hsq, hopen⟩
    have hadj : (horizontalStripCutRectangle M n).Adj u v :=
      (rectangleGraph_adj_iff (-(M : ℤ), 0) (2 * M) (2 * n) u v).2 hsq
    let e : (horizontalStripCutRectangle M n).edgeSet := ⟨s(u, v), hadj⟩
    have heq : horizontalStripRectangleOriginalEdge M n e =
        ⟨s(u.val, v.val), squareLattice.mem_edgeSet.mpr hsq⟩ := by
      exact horizontalStripRectangleOriginalEdge_eq_of_adj M n hadj
    have heA : e ∈ A := by
      apply (horizontalStripRectanglePlaneExtension_mem_originalEdge M n A e).mp
      simpa [heq] using hopen
    rw [FiniteFK.openGraph_adj]
    exact ⟨e, heA, rfl⟩
  · intro hopen
    rw [FiniteFK.openGraph_adj] at hopen
    rcases hopen with ⟨e, heA, heq⟩
    have hadj : (horizontalStripCutRectangle M n).Adj u v := by
      apply (horizontalStripCutRectangle M n).mem_edgeSet.mp
      simpa [heq] using e.property
    have hsq : squareLattice.Adj u.val v.val :=
      (rectangleGraph_adj_iff (-(M : ℤ), 0) (2 * M) (2 * n) u v).mp hadj
    have eeq : e = ⟨s(u, v), hadj⟩ := by
      apply Subtype.ext
      exact heq
    have heq' : horizontalStripRectangleOriginalEdge M n e =
        ⟨s(u.val, v.val), squareLattice.mem_edgeSet.mpr hsq⟩ := by
      rw [eeq]
      exact horizontalStripRectangleOriginalEdge_eq_of_adj M n hadj
    have hstate : horizontalStripRectanglePlaneExtension M n A
        (horizontalStripRectangleOriginalEdge M n e) = true :=
      (horizontalStripRectanglePlaneExtension_mem_originalEdge M n A e).mpr heA
    refine ⟨hsq, ?_⟩
    rw [← heq', hstate]

theorem horizontalStripRectangleOpenGraph_eq_openGraph
    (M n : ℕ) (A : Finset (horizontalStripCutRectangle M n).edgeSet) :
    horizontalStripRectangleOpenGraph M n (horizontalStripRectanglePlaneExtension M n A) =
      FiniteFK.openGraph (horizontalStripCutRectangle M n) A := by
  ext u v
  exact horizontalStripRectangleOpenGraph_adj_iff M n A u v

theorem horizontalStripRectangleActualConnected_iff
    (M n : ℕ) (A : Finset (horizontalStripCutRectangle M n).edgeSet)
    (u v : RectangleVertex (-(M : ℤ), 0) (2 * M) (2 * n)) :
    FiniteFK.ActualConnected (horizontalStripCutRectangle M n) A u v ↔
      (horizontalStripRectangleOpenGraph M n
        (horizontalStripRectanglePlaneExtension M n A)).Reachable u v := by
  rw [FiniteFK.ActualConnected, ← horizontalStripRectangleOpenGraph_eq_openGraph]

