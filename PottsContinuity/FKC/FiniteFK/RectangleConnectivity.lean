-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/RectangleConnectivity.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.RectangleEvents

@[expose] public section

namespace PottsContinuity.FKC.FiniteFK

open PottsContinuity.FKC

noncomputable section

variable (a : LatticeVertex) (w h : ℕ)

def rectangleGridVertex (i j : ℕ) (hi : i ≤ w) (hj : j ≤ h) : RectangleVertex a w h :=
  ⟨(a.1 + (i : ℤ), a.2 + (j : ℤ)), by
    rw [mem_latticeRectangle]
    constructor <;> constructor <;> omega⟩

private theorem rectangleGrid_horizontal_adj (i j : ℕ) (hi : i < w) (hj : j ≤ h) :
    (rectangleGraph a w h).Adj (rectangleGridVertex a w h i j (by omega) hj)
      (rectangleGridVertex a w h (i + 1) j (by omega) hj) := by
  rw [rectangleGraph_adj_iff, squareLattice_adj_iff]
  left
  constructor
  · left
    simp only [rectangleGridVertex, Subtype.coe_mk, Nat.cast_add, Nat.cast_one]
    ring
  · simp [rectangleGridVertex]

private theorem rectangleGrid_vertical_adj (i j : ℕ) (hi : i ≤ w) (hj : j < h) :
    (rectangleGraph a w h).Adj (rectangleGridVertex a w h i j hi (by omega))
      (rectangleGridVertex a w h i (j + 1) hi (by omega)) := by
  rw [rectangleGraph_adj_iff, squareLattice_adj_iff]
  right
  constructor
  · simp [rectangleGridVertex]
  · left
    simp only [rectangleGridVertex, Subtype.coe_mk, Nat.cast_add, Nat.cast_one]
    ring

private theorem rectangleGrid_horizontal_path (j : ℕ) (hj : j ≤ h) :
    ∀ i (hi : i ≤ w),
      (rectangleGraph a w h).Reachable (rectangleGridVertex a w h 0 j (by omega) hj)
        (rectangleGridVertex a w h i j hi hj) := by
  intro i
  induction i with
  | zero => intro; exact SimpleGraph.Reachable.refl _
  | succ i ih =>
    intro hi
    have hprev := ih (by omega)
    have hstep := (rectangleGrid_horizontal_adj a w h i j (by omega) hj).reachable
    exact hprev.trans hstep

private theorem rectangleGrid_vertical_path (i : ℕ) (hi : i ≤ w) :
    ∀ j (hj : j ≤ h),
      (rectangleGraph a w h).Reachable (rectangleGridVertex a w h i 0 hi (by omega))
        (rectangleGridVertex a w h i j hi hj) := by
  intro j
  induction j with
  | zero => intro; exact SimpleGraph.Reachable.refl _
  | succ j ih =>
    intro hj
    have hprev := ih (by omega)
    have hstep := (rectangleGrid_vertical_adj a w h i j hi (by omega)).reachable
    exact hprev.trans hstep

private theorem rectangleGrid_reachable (i j : ℕ) (hi : i ≤ w) (hj : j ≤ h) :
    (rectangleGraph a w h).Reachable (rectangleGridVertex a w h 0 0 (by omega) (by omega))
      (rectangleGridVertex a w h i j hi hj) := by
  exact (rectangleGrid_horizontal_path a w h 0 (by omega) i hi).trans
    (rectangleGrid_vertical_path a w h i hi j hj)

theorem rectangleGraph_reachable_all (u v : RectangleVertex a w h) :
    (rectangleGraph a w h).Reachable u v := by
  have hu := (mem_latticeRectangle a u.val w h).mp u.property
  have hv := (mem_latticeRectangle a v.val w h).mp v.property
  let iu := (u.val.1 - a.1).toNat
  let ju := (u.val.2 - a.2).toNat
  let iv := (v.val.1 - a.1).toNat
  let jv := (v.val.2 - a.2).toNat
  have hiu : iu ≤ w := by dsimp [iu]; have := hu.1.2; omega
  have hju : ju ≤ h := by dsimp [ju]; have := hu.2.2; omega
  have hiv : iv ≤ w := by dsimp [iv]; have := hv.1.2; omega
  have hjv : jv ≤ h := by dsimp [jv]; have := hv.2.2; omega
  have huval : rectangleGridVertex a w h iu ju hiu hju = u := by
    apply Subtype.ext
    dsimp [rectangleGridVertex, iu, ju]
    have := hu.1.1
    have := hu.2.1
    ext <;> simp <;> omega
  have hvval : rectangleGridVertex a w h iv jv hiv hjv = v := by
    apply Subtype.ext
    dsimp [rectangleGridVertex, iv, jv]
    have := hv.1.1
    have := hv.2.1
    ext <;> simp <;> omega
  have hbaseu := rectangleGrid_reachable a w h iu ju hiu hju
  have hbasev := rectangleGrid_reachable a w h iv jv hiv hjv
  calc
    (rectangleGraph a w h).Reachable u v := by
      rw [← huval, ← hvval]
      exact hbaseu.symm.trans hbasev

private theorem rectangleGraph_openGraph_univ_eq :
    openGraph (rectangleGraph a w h)
      (Finset.univ : Finset (rectangleGraph a w h).edgeSet) = rectangleGraph a w h := by
  classical
  let : Fintype ((rectangleGraph a w h).edgeSet) := Fintype.ofFinite _
  ext u v
  rw [openGraph_adj]
  constructor
  · rintro ⟨e, he, hval⟩
    have hedge : s(u, v) ∈ (rectangleGraph a w h).edgeSet := by
      rw [← hval]
      exact e.property
    exact (rectangleGraph a w h).mem_edgeSet.mp hedge
  · intro hadj
    have hedge : s(u, v) ∈ (rectangleGraph a w h).edgeSet := (rectangleGraph a w h).mem_edgeSet.mpr hadj
    exact ⟨⟨s(u, v), hedge⟩, by simp, rfl⟩

@[simp] theorem rectangleAllOpen_actualConnected (u v : RectangleVertex a w h) :
    ActualConnected (rectangleGraph a w h) (Finset.univ : Configuration (rectangleGraph a w h)) u v := by
  classical
  let : Fintype ((rectangleGraph a w h).edgeSet) := Fintype.ofFinite _
  rw [ActualConnected, rectangleGraph_openGraph_univ_eq]
  exact rectangleGraph_reachable_all a w h u v

end

end PottsContinuity.FKC.FiniteFK
