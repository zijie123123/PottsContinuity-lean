module

public import PottsContinuity.Thm3.Prop4.FKCRectangleOriginalRestriction
public import PottsContinuity.FKC.FiniteFK.RectangleDualCrossing
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Walk.Basic

/-!
# Rectangle noncrossing forces an actual closed-dual escape

The candidates are the w genuine bottom face ports. The alternative uses
only complementary states of sampled original rectangle bonds and applies
to every whole-plane configuration, with no probability or parameter input.
-/

@[expose] public section

namespace PottsContinuity.Thm3.Prop4

open PD.FK PD.FK.Medial
noncomputable section

/-- Integer face labels immediately below the sampled bottom horizontal bonds. -/
def rectangleBottomDualRoots (a : ℤ × ℤ) (w : ℕ) : Finset (ℤ × ℤ) :=
  (Finset.range w).image (fun i : ℕ => (a.1+(i : ℤ),a.2-1))

/-- The root union has no terminal-vertex cardinality loss. -/
theorem rectangleBottomDualRoots_card_le (a : ℤ × ℤ) (w : ℕ) :
    (rectangleBottomDualRoots a w).card ≤ w := by
  exact (Finset.card_image_le).trans_eq (Finset.card_range w)

private theorem dual_vertex_bounds (a : ℤ × ℤ) (w h : ℕ)
    (z : FKC.FiniteFK.RectangleDualVertex a w h) :
    a.1-1 ≤ z.val.1 ∧ z.val.1 ≤ a.1+w ∧ a.2-1 ≤ z.val.2 ∧ z.val.2 ≤ a.2+h := by
  have hz : z.val ∈ FKC.latticeRectangle (a.1-1,a.2-1) (w+1) (h+1) := z.property
  rw [FKC.mem_latticeRectangle] at hz
  dsimp at hz
  omega

/-- Noncrossing produces an actual original-state dual walk spanning the full face height. -/
theorem rectangle_noncrossing_original_dual_escape (a : ℤ × ℤ) (w h : ℕ)
    (ω : LatticeConfiguration) (hfail : ω ∉ BD12.horizontalRectangle a w h) :
    ∃ s ∈ rectangleBottomDualRoots a w, ∃ t : ℤ × ℤ,
      (h : ℤ)+1 ≤ max |t.1-s.1| |t.2-s.2| ∧
      ∃ q : (wholePlaneClosedDualGraph ω).Walk s t,
        ∀ z ∈ q.support,
          a.1-1 ≤ z.1 ∧ z.1 ≤ a.1+w ∧ a.2-1 ≤ z.2 ∧ z.2 ≤ a.2+h := by
  have hno : fkcRectangleRestriction a w h ω ∉ FKC.FiniteFK.rectangleHorizontalCrossingEvent a w h :=
    fun hc => hfail (fkc_rectangle_crossing_original a w h ω hc)
  obtain ⟨b,hb,t,ht,⟨p⟩⟩ := FKC.FiniteFK.rectangleDualBottomTop_of_no_primal_horizontal_crossing
    a w h (fkcRectangleRestriction a w h ω) hno
  obtain ⟨i,hi,hbi⟩ := Finset.mem_image.mp hb
  have himin : min i w = i := Nat.min_eq_left (by have := Finset.mem_range.mp hi; omega)
  have hbval : b.val = (a.1+(i : ℤ),a.2-1) := by
    rw [← hbi]
    simp only [FKC.FiniteFK.rectangleDualBottomPortVertex,himin]
  have hs : b.val ∈ rectangleBottomDualRoots a w :=
    Finset.mem_image.mpr ⟨i,hi,hbval.symm⟩
  obtain ⟨k,_,hkt⟩ := Finset.mem_image.mp ht
  have htval : t.val.2 = a.2+h := by rw [← hkt]; rfl
  have hdist : (h : ℤ)+1 ≤ max |t.val.1-b.val.1| |t.val.2-b.val.2| := by
    have he : t.val.2-b.val.2 = (h : ℤ)+1 := by rw [htval,hbval]; dsimp; omega
    have habs : |t.val.2-b.val.2| = (h : ℤ)+1 := by rw [he,abs_of_nonneg (by omega)]
    exact habs ▸ le_max_right _ _
  obtain ⟨q,hq⟩ := fkc_rectangle_dual_walk_original a w h (fkcRectangleRestriction a w h ω) ω
    (fkcRectangleRestriction_state a w h ω) p
    (fun z => a.1-1 ≤ z.1 ∧ z.1 ≤ a.1+w ∧ a.2-1 ≤ z.2 ∧ z.2 ≤ a.2+h)
    (fun z _ => dual_vertex_bounds a w h z)
  exact ⟨b.val,hs,t.val,hdist,q,hq⟩

end
end PottsContinuity.Thm3.Prop4
