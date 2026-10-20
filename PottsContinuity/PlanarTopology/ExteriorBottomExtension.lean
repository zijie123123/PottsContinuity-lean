module

public import PottsContinuity.PlanarTopology.BoundaryExtension
public import PottsContinuity.PlanarTopology.KSTCorridorTranspose
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Walk.Maps

@[expose] public section

namespace PottsContinuity.PlanarTopology
open PD.FK
noncomputable section

/-- Vertical connections between arbitrary integer heights, with exact support. -/
theorem vertical_walk_between (x a b : ℤ) :
    ∃ p : squareLattice.Walk (x,a) (x,b),
      ∀ z ∈ p.support, z.1 = x ∧ min a b ≤ z.2 ∧ z.2 ≤ max a b := by
  obtain ⟨p,hp⟩ := horizontal_walk_between a b x
  refine ⟨p.map latticeTransposeIso.toHom,?_⟩
  intro z hz
  rw [SimpleGraph.Walk.support_map] at hz
  obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hz
  have hh := hp w hw
  exact ⟨hh.2.2,hh.1,hh.2.1⟩

/-- A non-bottom point of the left three-piece boundary can be joined to a
lower exterior corner. Its top excursion stays to the left of its endpoint. -/
theorem left_boundary_to_lower_line (left right bottom top : ℤ) (u : LatticeVertex)
    (hbox : left ≤ u.1 ∧ u.1 ≤ right ∧ bottom ≤ u.2 ∧ u.2 ≤ top)
    (hboundary : u.1 = left ∨ u.2 = bottom ∨ u.2 = top) (hnot : u.2 ≠ bottom) :
    ∃ L : squareLattice.Walk (left-1,bottom-1) u,
      ∀ z ∈ L.support, bottom-1 ≤ z.2 ∧
        (z = u ∨ z.1 < left ∨ (top < z.2 ∧ z.1 ≤ u.1)) := by
  obtain ⟨s,L,hs,hLB,hLo⟩ := left_boundary_extension left right bottom top u hbox hboundary
  obtain ⟨V,hV⟩ := vertical_walk_between (left-1) (bottom-1) s.2
  have hs' : (left-1,s.2) = s := Prod.ext hs.symm rfl
  let W := V.copy rfl hs'
  refine ⟨W.append L,?_⟩
  intro z hz
  rw [SimpleGraph.Walk.mem_support_append_iff] at hz
  rcases hz with hz | hz
  · rw [SimpleGraph.Walk.support_copy] at hz
    have hh := hV z hz
    have hsy := (hLB s L.start_mem_support).2.2.1
    rw [min_eq_left hsy] at hh
    exact ⟨hh.2.1,Or.inr (Or.inl (by omega))⟩
  · refine ⟨(hLB z hz).2.2.1,?_⟩
    rcases hLo z hz with he | hx | ⟨hx,hy | hy⟩
    · exact Or.inl he
    · exact Or.inr (Or.inl hx)
    · exact (hnot hy.1).elim
    · exact Or.inr (Or.inr ⟨by omega,hx⟩)

/-- The right exterior extension, retaining the opposite top-coordinate order. -/
theorem right_boundary_to_lower_line (left right bottom top : ℤ) (u : LatticeVertex)
    (hbox : left ≤ u.1 ∧ u.1 ≤ right ∧ bottom ≤ u.2 ∧ u.2 ≤ top)
    (hboundary : u.1 = right ∨ u.2 = bottom ∨ u.2 = top) (hnot : u.2 ≠ bottom) :
    ∃ R : squareLattice.Walk (right+1,bottom-1) u,
      ∀ z ∈ R.support, bottom-1 ≤ z.2 ∧
        (z = u ∨ right < z.1 ∨ (top < z.2 ∧ u.1 ≤ z.1)) := by
  obtain ⟨s,R,hs,hRB,hRo⟩ := right_boundary_extension left right bottom top u hbox hboundary
  obtain ⟨V,hV⟩ := vertical_walk_between (right+1) (bottom-1) s.2
  have hs' : (right+1,s.2) = s := Prod.ext hs.symm rfl
  let W := V.copy rfl hs'
  refine ⟨W.append R,?_⟩
  intro z hz
  rw [SimpleGraph.Walk.mem_support_append_iff] at hz
  rcases hz with hz | hz
  · rw [SimpleGraph.Walk.support_copy] at hz
    have hh := hV z hz
    have hsy := (hRB s R.start_mem_support).2.2.1
    rw [min_eq_left hsy] at hh
    exact ⟨hh.2.1,Or.inr (Or.inl (by omega))⟩
  · refine ⟨(hRB z hz).2.2.1,?_⟩
    rcases hRo z hz with he | hx | ⟨hx,hy | hy⟩
    · exact Or.inl he
    · exact Or.inr (Or.inl hx)
    · exact (hnot hy.1).elim
    · exact Or.inr (Or.inr ⟨by omega,hx⟩)

end
end PottsContinuity.PlanarTopology
