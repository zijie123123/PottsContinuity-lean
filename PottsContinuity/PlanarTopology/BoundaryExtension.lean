module

public import PottsContinuity.PlanarTopology.HorizontalWalks
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Walk.Maps

@[expose] public section

namespace PottsContinuity.PlanarTopology
open PD.FK

/-- Extend a vertex on the left three-piece rectangle boundary to the expanded
left side. Apart from the original vertex, the extension stays outside the box. -/
theorem left_boundary_extension (left right bottom top : ℤ) (u : LatticeVertex)
    (hbox : left ≤ u.1 ∧ u.1 ≤ right ∧ bottom ≤ u.2 ∧ u.2 ≤ top)
    (hboundary : u.1 = left ∨ u.2 = bottom ∨ u.2 = top) :
    ∃ s, ∃ L : squareLattice.Walk s u, s.1 = left-1 ∧
      (∀ z ∈ L.support,
        left-1 ≤ z.1 ∧ z.1 ≤ right+1 ∧ bottom-1 ≤ z.2 ∧ z.2 ≤ top+1) ∧
      ∀ z ∈ L.support, z = u ∨ z.1 < left ∨
        (z.1 ≤ u.1 ∧ ((u.2 = bottom ∧ z.2 = bottom-1) ∨
          (u.2 = top ∧ z.2 = top+1))) := by
  rcases u with ⟨x,y⟩
  dsimp only [Prod.fst, Prod.snd] at hbox hboundary ⊢
  rcases hboundary with hx | hy | hy
  · subst x
    have hadj : squareLattice.Adj (left-1,y) (left,y) := by
      simp [squareLattice_adj_iff]
    refine ⟨(left-1,y), hadj.toWalk, rfl, ?_, ?_⟩
    · intro z hz
      have hz' : z = (left-1,y) ∨ z = (left,y) := by simpa using hz
      rcases hz' with rfl | rfl <;> dsimp <;> omega
    · intro z hz
      have hz' : z = (left-1,y) ∨ z = (left,y) := by simpa using hz
      rcases hz' with rfl | rfl
      · exact Or.inr (Or.inl (by dsimp; omega))
      · exact Or.inl rfl
  · subst y
    obtain ⟨L, hL⟩ := horizontal_walk_between (left-1) x (bottom-1)
    have hadj : squareLattice.Adj (x,bottom-1) (x,bottom) := by
      simp [squareLattice_adj_iff]
    refine ⟨(left-1,bottom-1), L.concat hadj, rfl, ?_, ?_⟩
    · intro z hz
      rw [SimpleGraph.Walk.support_concat] at hz
      rcases List.mem_append.mp hz with hz | hz
      · have h := hL z hz
        have hx : left-1 ≤ x := by omega
        rw [min_eq_left hx, max_eq_right hx] at h
        omega
      · have hz := List.mem_singleton.mp hz
        subst z
        dsimp
        omega
    · intro z hz
      rw [SimpleGraph.Walk.support_concat] at hz
      rcases List.mem_append.mp hz with hz | hz
      · have h := hL z hz
        have hx : left-1 ≤ x := by omega
        rw [min_eq_left hx, max_eq_right hx] at h
        exact Or.inr (Or.inr ⟨h.2.1, Or.inl ⟨rfl, h.2.2⟩⟩)
      · exact Or.inl (List.mem_singleton.mp hz)
  · subst y
    obtain ⟨L, hL⟩ := horizontal_walk_between (left-1) x (top+1)
    have hadj : squareLattice.Adj (x,top+1) (x,top) := by
      simp [squareLattice_adj_iff]
    refine ⟨(left-1,top+1), L.concat hadj, rfl, ?_, ?_⟩
    · intro z hz
      rw [SimpleGraph.Walk.support_concat] at hz
      rcases List.mem_append.mp hz with hz | hz
      · have h := hL z hz
        have hx : left-1 ≤ x := by omega
        rw [min_eq_left hx, max_eq_right hx] at h
        omega
      · have hz := List.mem_singleton.mp hz
        subst z
        dsimp
        omega
    · intro z hz
      rw [SimpleGraph.Walk.support_concat] at hz
      rcases List.mem_append.mp hz with hz | hz
      · have h := hL z hz
        have hx : left-1 ≤ x := by omega
        rw [min_eq_left hx, max_eq_right hx] at h
        exact Or.inr (Or.inr ⟨h.2.1, Or.inr ⟨rfl, h.2.2⟩⟩)
      · exact Or.inl (List.mem_singleton.mp hz)

 def reflectX : squareLattice →g squareLattice where
  toFun z := (-z.1,z.2)
  map_rel' := by
    intro a b h
    simp only [squareLattice_adj_iff] at h ⊢
    omega

/-- The corresponding exterior extension to the expanded right side. -/
theorem right_boundary_extension (left right bottom top : ℤ) (u : LatticeVertex)
    (hbox : left ≤ u.1 ∧ u.1 ≤ right ∧ bottom ≤ u.2 ∧ u.2 ≤ top)
    (hboundary : u.1 = right ∨ u.2 = bottom ∨ u.2 = top) :
    ∃ s, ∃ R : squareLattice.Walk s u, s.1 = right+1 ∧
      (∀ z ∈ R.support,
        left-1 ≤ z.1 ∧ z.1 ≤ right+1 ∧ bottom-1 ≤ z.2 ∧ z.2 ≤ top+1) ∧
      ∀ z ∈ R.support, z = u ∨ right < z.1 ∨
        (u.1 ≤ z.1 ∧ ((u.2 = bottom ∧ z.2 = bottom-1) ∨
          (u.2 = top ∧ z.2 = top+1))) := by
  obtain ⟨s, L, hs, hL, houtside⟩ := left_boundary_extension
    (-right) (-left) bottom top (-u.1,u.2)
    (by dsimp; omega) (by dsimp; omega)
  have hu : reflectX (-u.1,u.2) = u := by
    change (-(-u.1),u.2) = u
    ext <;> simp
  let R := (L.map reflectX).copy rfl hu
  have hsupp : R.support = L.support.map reflectX := by
    calc
      R.support = (L.map reflectX).support := SimpleGraph.Walk.support_copy _ _ _
      _ = L.support.map reflectX := SimpleGraph.Walk.support_map _ _
  refine ⟨reflectX s, R, ?_, ?_, ?_⟩
  · change -s.1 = right+1
    omega
  · intro z hz
    rw [hsupp] at hz
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hz
    have h := hL w hw
    change left-1 ≤ -w.1 ∧ -w.1 ≤ right+1 ∧ bottom-1 ≤ w.2 ∧ w.2 ≤ top+1
    omega
  · intro z hz
    rw [hsupp] at hz
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hz
    rcases houtside w hw with h | h | ⟨hx, h⟩
    · left
      rw [h]
      exact hu
    · right; left
      change right < -w.1
      omega
    · right; right
      change u.1 ≤ -w.1 ∧ _
      exact ⟨by dsimp at hx; omega, h⟩

end PottsContinuity.PlanarTopology
