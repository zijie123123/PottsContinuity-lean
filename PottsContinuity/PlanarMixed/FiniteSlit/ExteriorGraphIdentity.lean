module

public import PottsContinuity.PlanarMixed.FiniteSlit.ExteriorPortalNeighbors

@[expose] public section

namespace PottsContinuity.PlanarMixed.FiniteSlit
open PD.FK
noncomputable section

/-- The image graph attaches the left exterior exactly at its explicit portals. -/
theorem exteriorProjection_map_left_adj_iff (M : ℕ) (x y : ℤ) (w h : ℕ)
    (hM : 2 ≤ M) (hx : 1 ≤ x) (hxw : x ≤ (w:ℤ))
    (hleft : x-(M:ℤ) < 0) (hright : (w:ℤ) < x+(M:ℤ)-1) (hh : h < M)
    (u : RectangleVertex (0,0) w h) :
    ((graph M x y).map (exteriorProjection M x w h)).Adj (Sum.inl u) (Sum.inr false) ↔
      u ∈ sourceLeftPortal w h x := by
  constructor
  · intro hadj
    obtain ⟨_,a,b,hab,ha,hb⟩ := (SimpleGraph.map_adj' _ _ _ _).mp hadj
    exact left_exterior_neighbor_portal M x y w h hM hx hxw a b u
      ((exteriorProjection_eq_inl_iff M x w h a u).mp ha) hab hb
  · intro hu
    obtain ⟨b,hab,hb⟩ := left_portal_has_exterior_neighbor M x y w h hM hx hxw
      hleft hright hh u hu
    exact (SimpleGraph.map_adj' _ _ _ _).mpr ⟨by simp,_,b,hab,
      exteriorProjection_rectangleIntoReference M x w h (by omega) (by omega) (by omega) (by omega) u,hb⟩

/-- The image graph attaches the right exterior exactly at its explicit portals. -/
theorem exteriorProjection_map_right_adj_iff (M : ℕ) (x y : ℤ) (w h : ℕ)
    (hM : 2 ≤ M) (hx : 1 ≤ x) (hxw : x ≤ (w:ℤ))
    (hleft : x-(M:ℤ) < 0) (hright : (w:ℤ) < x+(M:ℤ)-1) (hh : h < M)
    (u : RectangleVertex (0,0) w h) :
    ((graph M x y).map (exteriorProjection M x w h)).Adj (Sum.inl u) (Sum.inr true) ↔
      u ∈ sourceRightPortal w h x := by
  constructor
  · intro hadj
    obtain ⟨_,a,b,hab,ha,hb⟩ := (SimpleGraph.map_adj' _ _ _ _).mp hadj
    exact right_exterior_neighbor_portal M x y w h hM hx hxw a b u
      ((exteriorProjection_eq_inl_iff M x w h a u).mp ha) hab hb
  · intro hu
    obtain ⟨b,hab,hb⟩ := right_portal_has_exterior_neighbor M x y w h hM hx hxw
      hleft hright hh u hu
    exact (SimpleGraph.map_adj' _ _ _ _).mpr ⟨by simp,_,b,hab,
      exteriorProjection_rectangleIntoReference M x w h (by omega) (by omega) (by omega) (by omega) u,hb⟩

/-- There is no image bond between either pair of exterior vertices. -/
theorem exteriorProjection_map_no_exterior_adj (M : ℕ) (x y : ℤ) (w h : ℕ)
    (hM : 2 ≤ M) (hx : 1 ≤ x) (hxw : x ≤ (w:ℤ)) (hyh : y ≤ (h:ℤ))
    (s t : Bool) :
    ¬ ((graph M x y).map (exteriorProjection M x w h)).Adj (Sum.inr s) (Sum.inr t) := by
  intro hadj
  obtain ⟨hne,a,b,hab,ha,hb⟩ := (SimpleGraph.map_adj' _ _ _ _).mp hadj
  cases s <;> cases t
  · exact hne rfl
  · exact opposite_exteriors_not_adj M x y w h hM hx hxw hyh a b ha hb hab
  · exact opposite_exteriors_not_adj M x y w h hM hx hxw hyh b a hb ha hab.symm
  · exact hne rfl

/-- Exact deterministic graph identity, independent of the containing
reference truncation. All original source vertices remain distinct. -/
theorem exteriorProjection_map_eq_sourceExteriorGraph (M : ℕ) (x y : ℤ) (w h : ℕ)
    (hM : 2 ≤ M) (hx : 1 ≤ x) (hxw : x ≤ (w:ℤ))
    (hleft : x-(M:ℤ) < 0) (hright : (w:ℤ) < x+(M:ℤ)-1) (hh : h < M)
    (hyh : y ≤ (h:ℤ)) :
    (graph M x y).map (exteriorProjection M x w h) = sourceExteriorGraph w h x y := by
  apply SimpleGraph.ext
  funext a b
  apply propext
  cases a with
  | inl u =>
    cases b with
    | inl v =>
      exact exteriorProjection_map_source_adj_iff M x y w h (by omega)
        (by omega) (by omega) (by omega) u v
    | inr s =>
      cases s
      · exact exteriorProjection_map_left_adj_iff M x y w h hM hx hxw hleft hright hh u
      · exact exteriorProjection_map_right_adj_iff M x y w h hM hx hxw hleft hright hh u
  | inr s =>
    cases b with
    | inl u =>
      rw [@SimpleGraph.adj_comm _ ((graph M x y).map (exteriorProjection M x w h)) (Sum.inr s) (Sum.inl u),
        @SimpleGraph.adj_comm _ (sourceExteriorGraph w h x y) (Sum.inr s) (Sum.inl u)]
      cases s
      · exact exteriorProjection_map_left_adj_iff M x y w h hM hx hxw hleft hright hh u
      · exact exteriorProjection_map_right_adj_iff M x y w h hM hx hxw hleft hright hh u
    | inr t =>
      exact iff_of_false (exteriorProjection_map_no_exterior_adj M x y w h hM hx hxw hyh s t)
        (sourceExteriorGraph_no_exterior_edge w h x y s t)

end
end PottsContinuity.PlanarMixed.FiniteSlit
