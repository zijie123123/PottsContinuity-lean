module

public import PottsContinuity.PlanarTopology.RectangleDualCoreGeometry
public import PottsContinuity.BD12.RectangleOpenGraphs
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

@[expose] public section

namespace PottsContinuity.PlanarTopology
open PD.FK PD.FK.Medial PD.Duality PD.RCInfinite BD12
noncomputable section

/-- Forgetting the finite true-dual carrier retains each original open bond
of a whole-plane restriction. -/
def rectangleDualRestrictionToInfiniteOpenHom (a : LatticeVertex) (w h : ℕ)
    (ω : LatticeConfiguration) :
    openGraph (rectangleDualGraph a w h)
      (embeddedRestriction _ (rectangleDualEdgeToSquareEdge a w h) ω) →g PD.rcInfiniteOpenGraph ω where
  toFun := Subtype.val
  map_rel' := by
    intro u v huv
    obtain ⟨e,he,hopen⟩ := (embeddedRestriction_openGraph_adj _ _ ω u v).mp huv
    have heq : (rectangleDualEdgeToSquareEdge a w h e).val = s(u.val,v.val) := by
      change Sym2.map (fun z : RectangleDualVertex a w h => z.val) e.val = _
      rw [he]
      rfl
    have hadj : s(u.val,v.val) ∈ PD.squareLattice.edgeSet :=
      heq ▸ (rectangleDualEdgeToSquareEdge a w h e).property
    apply (rcInfiniteOpenGraph_adj ω u.val v.val).mpr
    refine ⟨hadj,?_⟩
    have heq' : (⟨s(u.val,v.val),hadj⟩ : PD.squareLattice.edgeSet) =
        rectangleDualEdgeToSquareEdge a w h e := Subtype.ext heq.symm
    rwa [heq']

/-- True-dual connectivity contracts into connectivity using only original
open bonds inside the finite interior face box. Every noncollapsed edge keeps
both original endpoints; hence no new bond is declared open. -/
theorem rectangle_dual_reachable_core (a : LatticeVertex) (w h : ℕ)
    (hw : 1 ≤ w) (hh : 1 ≤ h) (ω : LatticeConfiguration)
    {u v : RectangleDualVertex a w h}
    (huv : (openGraph (rectangleDualGraph a w h)
      (embeddedRestriction _ (rectangleDualEdgeToSquareEdge a w h) ω)).Reachable u v) :
    ((PD.rcInfiniteOpenGraph ω).induce (rectangleDualInterior a w h : Set LatticeVertex)).Reachable
      ⟨rectangleCoreClamp a w h hw hh u.val,rectangleCoreClamp_mem_interior a w h hw hh u.val⟩
      ⟨rectangleCoreClamp a w h hw hh v.val,rectangleCoreClamp_mem_interior a w h hw hh v.val⟩ := by
  let f : RectangleDualVertex a w h → {z : LatticeVertex // z ∈ rectangleDualInterior a w h} :=
    fun z => ⟨rectangleCoreClamp a w h hw hh z.val,rectangleCoreClamp_mem_interior a w h hw hh z.val⟩
  apply reachable_map_of_eq_or_adj f _ huv
  intro x y hxy
  have hgraph := openGraph_le (rectangleDualGraph a w h)
    (embeddedRestriction _ (rectangleDualEdgeToSquareEdge a w h) ω) hxy
  rcases rectangleDualCoreClamp_step a w h hw hh x y hgraph with he | ⟨hx,hy⟩
  · exact Or.inl (Subtype.ext he)
  · right
    have hopen := (rectangleDualRestrictionToInfiniteOpenHom a w h ω).map_adj hxy
    change (PD.rcInfiniteOpenGraph ω).Adj (rectangleCoreClamp a w h hw hh x.val)
      (rectangleCoreClamp a w h hw hh y.val)
    rw [hx,hy]
    exact hopen

/-- The interior face box is exactly the smaller integer rectangle. The
positive-side premises include one-row and one-column cases honestly. -/
theorem rectangleDualInterior_eq_rectangle (a : LatticeVertex) (w h : ℕ)
    (hw : 1 ≤ w) (hh : 1 ≤ h) :
    rectangleDualInterior a w h = latticeRectangle a (w-1) (h-1) := by
  ext z
  simp only [rectangleDualInterior,rectangleDualExpanded,Finset.mem_filter,mem_latticeRectangle]
  push_cast
  omega

end
end PottsContinuity.PlanarTopology
