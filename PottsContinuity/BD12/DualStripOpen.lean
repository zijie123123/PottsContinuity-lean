module

public import PottsContinuity.BD12.DualStrip
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-! True-dual port crossings give ordinary vertical strip crossings. -/

@[expose] public section

namespace PottsContinuity.BD12

open PD.FK PD.FK.Medial PD.Duality PD.RCInfinite

noncomputable section

/-- Actual bottom-to-top crossing in the induced whole-plane open graph. -/
def verticalRectangle (a : LatticeVertex) (w h : ℕ) : Set LatticeConfiguration :=
  {ω | ∃ u v : RectangleVertex a w h,
    u.val.2 = a.2 ∧ v.val.2 = a.2 + (h : ℤ) ∧
      ((PD.rcInfiniteOpenGraph ω).induce
        (latticeRectangle a w h : Set LatticeVertex)).Reachable u v}

theorem verticalRectangle_isCylinder (a : LatticeVertex) (w h : ℕ) :
    IsCylinder (verticalRectangle a w h) := by
  have heq : verticalRectangle a w h =
      embeddedRestriction (rectangleGraph a w h)
        (frozenEdgeEmbedding (latticeRectangle a w h)) ⁻¹'
      {A | ∃ u v : RectangleVertex a w h,
        u.val.2 = a.2 ∧ v.val.2 = a.2 + (h : ℤ) ∧
          ActualConnected (rectangleGraph a w h) A u v} := by
    ext ω
    change _ ↔ ∃ u v, _ ∧ _ ∧
      (openGraph _ (embeddedRestriction _ _ ω)).Reachable u v
    have hg := embeddedRestriction_domainGraph (latticeRectangle a w h) ω
    change openGraph (rectangleGraph a w h)
      (embeddedRestriction (rectangleGraph a w h)
        (frozenEdgeEmbedding (latticeRectangle a w h)) ω) = _ at hg
    rw [hg]
    rfl
  rw [heq]
  exact embeddedRestriction_isCylinder _ _ _

theorem dualRestriction_adj (a : LatticeVertex) (w h : ℕ)
    (ω : LatticeConfiguration) {u v : RectangleDualVertex a w h}
    (huv : (openGraph (rectangleDualGraph a w h)
      (embeddedRestriction _ (rectangleDualEdgeToSquareEdge a w h) ω)).Adj u v) :
    (PD.rcInfiniteOpenGraph ω).Adj u.val v.val := by
  obtain ⟨e, he, ho⟩ := (embeddedRestriction_openGraph_adj _ _ ω u v).mp huv
  have heq : (rectangleDualEdgeToSquareEdge a w h e).val = s(u.val, v.val) := by
    change Sym2.map Subtype.val e.val = _
    rw [he]
    rfl
  rw [rcInfiniteOpenGraph_adj]
  have hedge : s(u.val, v.val) ∈ PD.squareLattice.edgeSet :=
    heq ▸ (rectangleDualEdgeToSquareEdge a w h e).property
  refine ⟨hedge, ?_⟩
  have heq' : rectangleDualEdgeToSquareEdge a w h e = ⟨s(u.val, v.val), hedge⟩ :=
    Subtype.ext heq
  exact heq' ▸ ho

theorem dualStripProjection_open (a : LatticeVertex) (n h : ℕ)
    (ω : LatticeConfiguration) {u v : RectangleDualVertex a (n + 1) h}
    (huv : (openGraph (rectangleDualGraph a (n + 1) h)
      (embeddedRestriction _ (rectangleDualEdgeToSquareEdge a (n + 1) h) ω)).Adj u v) :
    dualStripProjection a n h u = dualStripProjection a n h v ∨
      ((PD.rcInfiniteOpenGraph ω).induce
        (latticeRectangle (a.1, a.2 - 1) n (h + 1) : Set LatticeVertex)).Adj
          (dualStripProjection a n h u) (dualStripProjection a n h v) := by
  rcases dualStripProjection_edge a n h (openGraph_le _ _ huv) with h | ⟨hu, hv⟩
  · exact Or.inl h
  · right
    change (PD.rcInfiniteOpenGraph ω).Adj
      (dualStripProjection a n h u).val (dualStripProjection a n h v).val
    rw [hu, hv]
    exact dualRestriction_adj a (n + 1) h ω huv

/-- Contracting dangling side edges preserves an actual port-to-port crossing.
The resulting strip has width n and height h+1 for a primal width n+1. -/
theorem dualPortRectangle_subset_vertical (a : LatticeVertex) (n h : ℕ) :
    dualPortRectangle a (n + 1) h ⊆ verticalRectangle (a.1, a.2 - 1) n (h + 1) := by
  rintro ω ⟨b, hb, t, ht, hbt⟩
  refine ⟨dualStripProjection a n h b, dualStripProjection a n h t, ?_, ?_, ?_⟩
  · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hb
    rfl
  · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ht
    change a.2 + (h : ℤ) = a.2 - 1 + ((h + 1 : ℕ) : ℤ)
    omega
  · exact reachable_map_of_eq_or_adj (dualStripProjection a n h)
      (dualStripProjection_open a n h ω) hbt

end
end PottsContinuity.BD12
