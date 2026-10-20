module

public import PottsContinuity.PlanarTopology.ExteriorBottomExtension
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-! # Connected exterior face labels of a finite lattice rectangle -/

@[expose] public section

namespace PottsContinuity.Thm3.Prop4
open PD.FK PlanarTopology

/-- Face bases outside the interior face rectangle. Outer sampled face ports
and the four unused exterior corners all lie in this geometric set. -/
def rectangleExteriorFaces (a : LatticeVertex) (w h : ℕ) : Set LatticeVertex :=
  {f | f.1 < a.1 ∨ a.1+(w : ℤ) ≤ f.1 ∨ f.2 < a.2 ∨ a.2+(h : ℤ) ≤ f.2}

/-- Every face in the exterior joins the fixed lower-left exterior corner
without entering the interior face rectangle. -/
theorem rectangleExteriorFaces_reachable_corner (a : LatticeVertex) (w h : ℕ)
    (f : rectangleExteriorFaces a w h) :
    (squareLattice.induce (rectangleExteriorFaces a w h)).Reachable f
      ⟨(a.1-1,a.2-1),Or.inl (by omega)⟩ := by
  have horizontalCase (hy : f.val.2 < a.2 ∨ a.2+(h : ℤ) ≤ f.val.2) :
      (squareLattice.induce (rectangleExteriorFaces a w h)).Reachable f
        ⟨(a.1-1,a.2-1),Or.inl (by omega)⟩ := by
    obtain ⟨p,hp⟩ := horizontal_walk_between f.val.1 (a.1-1) f.val.2
    obtain ⟨q,hq⟩ := vertical_walk_between (a.1-1) f.val.2 (a.2-1)
    have hsupp : ∀ z ∈ (p.append q).support, z ∈ rectangleExteriorFaces a w h := by
      intro z hz
      rw [SimpleGraph.Walk.mem_support_append_iff] at hz
      rcases hz with hz | hz
      · have hyz := (hp z hz).2.2
        rcases hy with hy | hy
        · exact Or.inr (Or.inr (Or.inl (by omega)))
        · exact Or.inr (Or.inr (Or.inr (by omega)))
      · exact Or.inl (by have := (hq z hz).1; omega)
    exact ⟨(p.append q).induce _ hsupp⟩
  have verticalCase (hx : f.val.1 < a.1 ∨ a.1+(w : ℤ) ≤ f.val.1) :
      (squareLattice.induce (rectangleExteriorFaces a w h)).Reachable f
        ⟨(a.1-1,a.2-1),Or.inl (by omega)⟩ := by
    obtain ⟨p,hp⟩ := vertical_walk_between f.val.1 f.val.2 (a.2-1)
    obtain ⟨q,hq⟩ := horizontal_walk_between f.val.1 (a.1-1) (a.2-1)
    have hsupp : ∀ z ∈ (p.append q).support, z ∈ rectangleExteriorFaces a w h := by
      intro z hz
      rw [SimpleGraph.Walk.mem_support_append_iff] at hz
      rcases hz with hz | hz
      · have hxz := (hp z hz).1
        rcases hx with hx | hx
        · exact Or.inl (by omega)
        · exact Or.inr (Or.inl (by omega))
      · exact Or.inr (Or.inr (Or.inl (by have := (hq z hz).2.2; omega)))
    exact ⟨(p.append q).induce _ hsupp⟩
  rcases f.property with hleft | hright | hbottom | htop
  · exact verticalCase (Or.inl hleft)
  · exact verticalCase (Or.inr hright)
  · exact horizontalCase (Or.inl hbottom)
  · exact horizontalCase (Or.inr htop)

/-- The entire face-label lattice is connected through original unit steps. -/
theorem face_label_lattice_preconnected : squareLattice.Preconnected := by
  intro x y
  obtain ⟨p,_⟩ := horizontal_walk_between x.1 y.1 x.2
  obtain ⟨q,_⟩ := vertical_walk_between y.1 x.2 y.2
  exact (p.append q).reachable

end PottsContinuity.Thm3.Prop4
