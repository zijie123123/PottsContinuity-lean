module

public import PottsContinuity.Thm3.Prop4.MarkedLowerFaceCells

/-! # Exact exterior labels of the marked lower reached-region cells -/

@[expose] public section

namespace PottsContinuity.Thm3.Prop4
open PD.FK
noncomputable section

/-- The lower reached region retains all lower exterior seeds and excludes
all upper exterior seeds on a genuine marked connection. -/
theorem sampledLowerRegion_exterior_labels (a : LatticeVertex) (w h : ℕ)
    (u v : RectangleVertex a w h) (hu : u.val.1 = a.1) (hv : v.val.1 = a.1+(w : ℤ))
    (A : Configuration (rectangleGraph a w h)) (hA : ActualConnected (rectangleGraph a w h) A u v) :
    (∀ f ∈ PlanarTopology.rectangleLowerDualArc a w h u.val v.val,
      sampledDualSeedRegion a w h A (PlanarTopology.rectangleLowerDualArc a w h u.val v.val) f) ∧
    (∀ f ∈ PlanarTopology.rectangleUpperDualArc a w h u.val v.val,
      ¬sampledDualSeedRegion a w h A (PlanarTopology.rectangleLowerDualArc a w h u.val v.val) f) := by
  refine ⟨fun f hf => ⟨f,hf,SimpleGraph.Reachable.refl _⟩,?_⟩
  intro f hf hreg
  exact Set.disjoint_left.mp (sampledDualSeedRegions_disjoint_of_marked_connection a w h A u v hu hv hA)
    hreg ⟨f,hf,SimpleGraph.Reachable.refl _⟩

/-- Adding only the two unused bottom corner cells yields precisely the
exterior labels with jumps at the prescribed side marks. -/
theorem markedLowerFaceCells_side_labels_of_arc_labels (a : LatticeVertex) (w h : ℕ)
    (hw : 1 ≤ w) (hh : 1 ≤ h) (u v : RectangleVertex a w h)
    (_hu : u.val.1 = a.1) (hv : v.val.1 = a.1+(w : ℤ))
    (P : LatticeVertex → Prop)
    (hlower : ∀ f ∈ PlanarTopology.rectangleLowerDualArc a w h u.val v.val, P f)
    (hupper : ∀ f ∈ PlanarTopology.rectangleUpperDualArc a w h u.val v.val, ¬P f) :
    let S := markedLowerFaceCells a w h (P)
    (∀ y : ℤ, a.2-1 ≤ y → y ≤ a.2+(h : ℤ) → ((a.1-1,y) ∈ S ↔ y < u.val.2)) ∧
    (∀ y : ℤ, a.2-1 ≤ y → y ≤ a.2+(h : ℤ) → ((a.1+(w : ℤ),y) ∈ S ↔ y < v.val.2)) ∧
    (∀ x : ℤ, a.1-1 ≤ x → x ≤ a.1+(w : ℤ) → (x,a.2-1) ∈ S) ∧
    (∀ x : ℤ, a.1-1 ≤ x → x ≤ a.1+(w : ℤ) → (x,a.2+(h : ℤ)) ∉ S) := by
  dsimp only
  have ub := (PD.FK.mem_latticeRectangle a u.val w h).mp u.property
  have vb := (PD.FK.mem_latticeRectangle a v.val w h).mp v.property
  have hleftP (y : ℤ) (hy : a.2 ≤ y) (hyt : y < a.2+(h : ℤ)) :
      P (a.1-1,y) ↔ y < u.val.2 := by
    by_cases hlt : y < u.val.2
    · exact iff_of_true (hlower _ (Or.inr (Or.inl ⟨rfl,hy,hyt,hlt⟩))) hlt
    · have hseed : (a.1-1,y) ∈ PlanarTopology.rectangleUpperDualArc a w h u.val v.val := by
        dsimp [PlanarTopology.rectangleUpperDualArc]
        exact Or.inr (Or.inl ⟨rfl,hy,by omega,hyt⟩)
      exact iff_of_false (hupper _ hseed) hlt
  have hrightP (y : ℤ) (hy : a.2 ≤ y) (hyt : y < a.2+(h : ℤ)) :
      P (a.1+(w : ℤ),y) ↔ y < v.val.2 := by
    by_cases hlt : y < v.val.2
    · exact iff_of_true (hlower _ (Or.inr (Or.inr ⟨rfl,hy,hyt,hlt⟩))) hlt
    · have hseed : (a.1+(w : ℤ),y) ∈ PlanarTopology.rectangleUpperDualArc a w h u.val v.val := by
        dsimp [PlanarTopology.rectangleUpperDualArc]
        exact Or.inr (Or.inr ⟨rfl,hy,by omega,hyt⟩)
      exact iff_of_false (hupper _ hseed) hlt
  refine ⟨?_,?_,?_,?_⟩
  · intro y hlo hhi
    rw [mem_markedLowerFaceCells]
    simp only [Prod.mk.injEq,true_and]
    by_cases hb : y = a.2-1
    · omega
    · by_cases ht : y = a.2+(h : ℤ)
      · omega
      · have hp := hleftP y (by omega) (by omega)
        rw [hp]
        omega
  · intro y hlo hhi
    rw [mem_markedLowerFaceCells]
    simp only [Prod.mk.injEq,true_and]
    by_cases hb : y = a.2-1
    · omega
    · by_cases ht : y = a.2+(h : ℤ)
      · omega
      · have hp := hrightP y (by omega) (by omega)
        rw [hp]
        omega
  · intro x hlo hhi
    rw [mem_markedLowerFaceCells]
    simp only [Prod.mk.injEq]
    by_cases hx : a.1 ≤ x ∧ x < a.1+(w : ℤ)
    · have hp := hlower (x,a.2-1) (Or.inl ⟨rfl,hx.1,hx.2⟩)
      simp only [hp,and_true]
      omega
    · by_cases hp : P (x,a.2-1) <;>
        simp only [hp,and_true,and_false,or_false] <;> omega
  · intro x hlo hhi
    rw [mem_markedLowerFaceCells]
    simp only [Prod.mk.injEq]
    by_cases hx : a.1 ≤ x ∧ x < a.1+(w : ℤ)
    · have hp := hupper (x,a.2+(h : ℤ)) (Or.inl ⟨rfl,hx.1,hx.2⟩)
      simp only [hp,and_false,or_false]
      omega
    · by_cases hp : P (x,a.2+(h : ℤ)) <;>
        simp only [hp,and_true,and_false,or_false] <;> omega

end
end PottsContinuity.Thm3.Prop4
