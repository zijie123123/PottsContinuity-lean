module

public import PottsContinuity.PlanarMixed.FiniteSlit.RectangleClipping
public import PottsContinuity.PlanarMixed.CutRegionCollapse

/-! Collapse of the two geometric reference exteriors. Original source
vertices remain distinct; false and true label the left and right exteriors. -/

@[expose] public section

namespace PottsContinuity.PlanarMixed.FiniteSlit
open PD.FK
noncomputable section

/-- The source carrier with two auxiliary exterior vertices, used only for
deterministic reachability, never as a sampled FK graph. -/
abbrev ExteriorVertex (w h : ℕ) := RectangleVertex (0,0) w h ⊕ Bool

/-- Keep each source vertex and collapse every outside vertex to its actual
side of the slit. Both outside cases are explicit on the whole carrier. -/
def exteriorProjection (M : ℕ) (x : ℤ) (w h : ℕ) : Vertex M x → ExteriorVertex w h := by
  classical
  exact fun v => if hv : v.val ∈ PD.FK.latticeRectangle (0,0) w h then
    Sum.inl ⟨v.val,hv⟩ else if v.val.1 < x then Sum.inr false else Sum.inr true

/-- An original source vertex has a singleton fibre, retaining its coordinates. -/
theorem exteriorProjection_eq_inl_iff (M : ℕ) (x : ℤ) (w h : ℕ)
    (v : Vertex M x) (u : RectangleVertex (0,0) w h) :
    exteriorProjection M x w h v = Sum.inl u ↔ v.val = u.val := by
  classical
  by_cases hv : v.val ∈ PD.FK.latticeRectangle (0,0) w h
  · simp only [exteriorProjection,dite_eq_left hv,Sum.inl.injEq,Subtype.ext_iff]
  · have hn : v.val ≠ u.val := by
      intro he
      apply hv
      rw [he]
      exact u.property
    by_cases hc : v.val.1 < x <;> simp [exteriorProjection,hv,hn,hc]

/-- The left exterior fibre is exactly the outside vertices left of the slit. -/
theorem exteriorProjection_eq_left_iff (M : ℕ) (x : ℤ) (w h : ℕ) (v : Vertex M x) :
    exteriorProjection M x w h v = Sum.inr false ↔
      v.val ∉ PD.FK.latticeRectangle (0,0) w h ∧ v.val.1 < x := by
  classical
  unfold exteriorProjection
  split_ifs <;> simp_all

/-- The right exterior fibre is the complementary outside side of the slit. -/
theorem exteriorProjection_eq_right_iff (M : ℕ) (x : ℤ) (w h : ℕ) (v : Vertex M x) :
    exteriorProjection M x w h v = Sum.inr true ↔
      v.val ∉ PD.FK.latticeRectangle (0,0) w h ∧ x ≤ v.val.1 := by
  classical
  unfold exteriorProjection
  split_ifs <;> simp_all

/-- The canonical coordinate inclusion is a section of the projection. -/
theorem exteriorProjection_rectangleIntoReference (M : ℕ) (x : ℤ) (w h : ℕ)
    (hM : 1 ≤ M) (hleft : x-(M:ℤ) ≤ 0) (hright : (w:ℤ) ≤ x+(M:ℤ)-1)
    (hheight : h ≤ M) (u : RectangleVertex (0,0) w h) :
    exteriorProjection M x w h
      (rectangleIntoReference M x w h hM hleft hright hheight u) = Sum.inl u :=
  (exteriorProjection_eq_inl_iff M x w h _ u).mpr rfl

/-- Source cuts have exactly their original coordinate-image preimages;
neither of the auxiliary exterior vertices belongs to a source cut. -/
theorem exteriorProjection_preimage_cut (M : ℕ) (x : ℤ) (w h : ℕ)
    (hM : 1 ≤ M) (hleft : x-(M:ℤ) ≤ 0) (hright : (w:ℤ) ≤ x+(M:ℤ)-1)
    (hheight : h ≤ M) (cut : Set (RectangleVertex (0,0) w h)) :
    (exteriorProjection M x w h) ⁻¹' (Sum.inl '' cut) =
      rectangleIntoReference M x w h hM hleft hright hheight '' cut := by
  ext v
  constructor
  · rintro ⟨u,hu,hπ⟩
    have hv := (exteriorProjection_eq_inl_iff M x w h v u).mp hπ.symm
    exact ⟨u,hu,Subtype.ext hv.symm⟩
  · rintro ⟨u,hu,rfl⟩
    exact ⟨u,hu,(exteriorProjection_rectangleIntoReference M x w h hM hleft hright hheight u).symm⟩

end
end PottsContinuity.PlanarMixed.FiniteSlit
