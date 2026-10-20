module

public import PottsContinuity.PlanarTopology.RectangleConnectionEvents
public import PottsContinuity.PlanarTopology.OpenGraphMonotonicity
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

@[expose] public section

namespace PottsContinuity.PlanarTopology
open PD.FK PD.RCInfinite BD12
noncomputable section

/-- A walk leaving a domain reaches an inside boundary vertex along an
actual walk entirely contained in that domain. -/
theorem walk_reaches_inner_boundary {V : Type*} {G : SimpleGraph V}
    {u v : V} (p : G.Walk u v) (D : Set V) (hu : u ∈ D) (hv : v ∉ D) :
    ∃ z ∈ D, ∃ t ∉ D, G.Adj z t ∧ ∃ r : G.Walk u z, ∀ x ∈ r.support, x ∈ D := by
  induction p with
  | nil => exact (hv hu).elim
  | @cons u w v huw p ih =>
    by_cases hw : w ∈ D
    · obtain ⟨z,hz,t,ht,hzt,r,hr⟩ := ih hw hv
      refine ⟨z,hz,t,ht,hzt,r.cons huw,?_⟩
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact hu
      · exact hr x hx
    · exact ⟨u,hu,w,hw,huw,.nil,by simpa using hu⟩

/-- An original lattice edge leaving a closed rectangle starts on one of
its four literal sides, including all zero-side-length cases. -/
theorem latticeRectangle_exit_on_side (a z t : LatticeVertex) (w h : ℕ)
    (hz : z ∈ latticeRectangle a w h) (ht : t ∉ latticeRectangle a w h)
    (hadj : PD.squareLattice.Adj z t) :
    z.1 = a.1 ∨ z.1 = a.1+(w:ℤ) ∨ z.2 = a.2 ∨ z.2 = a.2+(h:ℤ) := by
  have hz' := (mem_latticeRectangle a z w h).mp hz
  have ht' : ¬((a.1 ≤ t.1 ∧ t.1 ≤ a.1+(w:ℤ)) ∧ (a.2 ≤ t.2 ∧ t.2 ≤ a.2+(h:ℤ))) := by
    intro ht'
    exact ht ((mem_latticeRectangle a t w h).mpr ht')
  rw [squareLattice_adj_iff] at hadj
  omega

/-- Every actual infinite root in a contained marked set reaches a literal
rectangle side using only original open bonds inside the rectangle. -/
theorem infiniteHit_subset_rectangle_side_union (a : LatticeVertex) (w h : ℕ)
    (S : Set LatticeVertex) (hS : S ⊆ latticeRectangle a w h) :
    infiniteHit S ⊆
      rectangleConnectionEvent a w h S {z | z.1 = a.1} ∪
      rectangleConnectionEvent a w h S {z | z.1 = a.1+(w:ℤ)} ∪
      rectangleConnectionEvent a w h S {z | z.2 = a.2} ∪
      rectangleConnectionEvent a w h S {z | z.2 = a.2+(h:ℤ)} := by
  intro ω hω
  obtain ⟨u,hu,hi⟩ := hω
  have huR := hS hu
  obtain ⟨v,hv,hvR⟩ := hi.exists_notMem_finset (latticeRectangle a w h)
  obtain ⟨p⟩ := hv
  obtain ⟨z,hz,t,ht,hzt,r,hr⟩ := walk_reaches_inner_boundary p
    (latticeRectangle a w h : Set LatticeVertex) huR hvR
  have hc (T : Set LatticeVertex) (hzT : z ∈ T) : ω ∈ rectangleConnectionEvent a w h S T := by
    apply (rectangleConnectionEvent_iff a w h S T ω).mpr
    exact ⟨⟨u,huR⟩,hu,⟨z,hz⟩,hzT,⟨r.induce _ hr⟩⟩
  obtain ⟨he,_⟩ := (rcInfiniteOpenGraph_adj ω z t).mp hzt
  rcases latticeRectangle_exit_on_side a z t w h hz ht (PD.squareLattice.mem_edgeSet.mp he) with
    hzL | hzR | hzB | hzT
  · exact Or.inl (Or.inl (Or.inl (hc _ hzL)))
  · exact Or.inl (Or.inl (Or.inr (hc _ hzR)))
  · exact Or.inl (Or.inr (hc _ hzB))
  · exact Or.inr (hc _ hzT)

end
end PottsContinuity.PlanarTopology
