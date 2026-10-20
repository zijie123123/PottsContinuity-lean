module

public import PottsContinuity.PlanarMixed.FiniteSlit.ExteriorProjection
public import PottsContinuity.PlanarMixed.FiniteSlit.VerticalPaths

@[expose] public section

namespace PottsContinuity.PlanarMixed.FiniteSlit
open PD.FK
noncomputable section

/-- The actual top-left original reference vertex. -/
def leftTop (M : ℕ) (x : ℤ) (hM : 1 ≤ M) : Vertex M x :=
  ⟨(x-(M:ℤ),(M:ℤ)),by rw [mem_rectangle_iff M x hM]; dsimp; omega⟩

/-- The actual top-right original reference vertex. -/
def rightTop (M : ℕ) (x : ℤ) (hM : 1 ≤ M) : Vertex M x :=
  ⟨(x+(M:ℤ)-1,(M:ℤ)),by rw [mem_rectangle_iff M x hM]; dsimp; omega⟩

/-- No vertex of the reference lies below the source bottom. Outside-source
membership is therefore exactly a side or top coordinate inequality. -/
theorem outside_source_iff (M : ℕ) (x : ℤ) (w h : ℕ) (hM : 1 ≤ M) (u : Vertex M x) :
    u.val ∉ PD.FK.latticeRectangle (0,0) w h ↔
      u.val.1 < 0 ∨ (w:ℤ) < u.val.1 ∨ (h:ℤ) < u.val.2 := by
  have hu := (mem_rectangle_iff M x hM u.val).mp u.property
  rw [PD.FK.mem_latticeRectangle]
  dsimp
  omega

/-- An outside vertex reaches a top corner on the same slit side using
only original outside bonds: first vertically, then horizontally at the top. -/
theorem outside_walk_to_top (M : ℕ) (x y : ℤ) (w h : ℕ) (hM : 2 ≤ M)
    (hh : h < M) (u t : Vertex M x) (ht : t.val.2 = (M:ℤ))
    (hu : u.val ∉ PD.FK.latticeRectangle (0,0) w h)
    (hside : (u.val.1 < x ∧ t.val.1 < x) ∨ (x ≤ u.val.1 ∧ x ≤ t.val.1)) :
    ∃ p : (graph M x y).Walk u t, ∀ z ∈ p.support,
      z.val ∉ PD.FK.latticeRectangle (0,0) w h ∧
        ((u.val.1 < x ∧ z.val.1 < x) ∨ (x ≤ u.val.1 ∧ x ≤ z.val.1)) := by
  have hub := (mem_rectangle_iff M x (by omega) u.val).mp u.property
  have hu' := (outside_source_iff M x w h (by omega) u).mp hu
  let v : Vertex M x := ⟨(u.val.1,(M:ℤ)),by
    rw [mem_rectangle_iff M x (by omega)]
    dsimp
    omega⟩
  obtain ⟨P,hP⟩ := vertical_walk M x y hM u v rfl
  obtain ⟨Q,hQ⟩ := horizontal_walk M x y hM v t (by exact ht.symm) (by
    rcases hside with hl | hr
    · exact Or.inl ⟨by change u.val.1 ≤ x-1; omega,by omega⟩
    · exact Or.inr hr)
  refine ⟨P.append Q,?_⟩
  intro z hz
  rw [SimpleGraph.Walk.mem_support_append_iff] at hz
  rcases hz with hz | hz
  · have hp := hP z hz
    change z.val.1 = u.val.1 ∧ min u.val.2 (M:ℤ) ≤ z.val.2 ∧
      z.val.2 ≤ max u.val.2 (M:ℤ) at hp
    rw [min_eq_left hub.2.2.2] at hp
    refine ⟨(outside_source_iff M x w h (by omega) z).mpr (by omega),?_⟩
    rcases hside with hl | hr
    · exact Or.inl ⟨hl.1,by omega⟩
    · exact Or.inr ⟨hr.1,by omega⟩
  · have hq := hQ z hz
    change min u.val.1 t.val.1 ≤ z.val.1 ∧ z.val.1 ≤ max u.val.1 t.val.1 ∧
      z.val.2 = (M:ℤ) at hq
    refine ⟨(outside_source_iff M x w h (by omega) z).mpr (Or.inr (Or.inr (by omega))),?_⟩
    rcases hside with hl | hr
    · exact Or.inl ⟨hl.1,by omega⟩
    · exact Or.inr ⟨hr.1,by omega⟩

end
end PottsContinuity.PlanarMixed.FiniteSlit
