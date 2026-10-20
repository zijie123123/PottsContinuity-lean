module

public import PottsContinuity.PlanarTopology.ExteriorBottomExtension
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

@[expose] public section

namespace PottsContinuity.Push
open PottsContinuity.PD.FK

/-- Every two original rectangle vertices have a genuine original rectangle
walk, including degenerate widths and heights. -/
theorem rectangle_graph_preconnected (a : LatticeVertex) (w h : ℕ) :
    (rectangleGraph a w h).Preconnected := by
  intro u v
  obtain ⟨p,hp⟩ := PlanarTopology.horizontal_walk_between u.val.1 v.val.1 u.val.2
  obtain ⟨q,hq⟩ := PlanarTopology.vertical_walk_between v.val.1 u.val.2 v.val.2
  have hu := (mem_latticeRectangle a u.val w h).mp u.property
  have hv := (mem_latticeRectangle a v.val w h).mp v.property
  have hsupp : ∀ z ∈ (p.append q).support, z ∈ PD.FK.latticeRectangle a w h := by
    intro z hz
    rw [SimpleGraph.Walk.mem_support_append_iff] at hz
    rw [mem_latticeRectangle]
    rcases hz with hz | hz
    · obtain ⟨hx,hx',hy⟩ := hp z hz
      constructor <;> constructor <;> omega
    · obtain ⟨hx,hy,hy'⟩ := hq z hz
      constructor <;> constructor <;> omega
  exact ⟨(p.append q).induce (PD.FK.latticeRectangle a w h : Set LatticeVertex) hsupp⟩

end PottsContinuity.Push
