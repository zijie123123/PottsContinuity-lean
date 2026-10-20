module

public import PottsContinuity.PlanarTopology.KSTCurveIntersection
public import Mathlib.Tactic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Combinatorics.SimpleGraph.Walk.Maps
public import Mathlib.Order.CompletePartialOrder

@[expose] public section

namespace PottsContinuity.PlanarTopology
open PD.FK PD.FK.Medial PD.FK.Curves
noncomputable section

/-- An actual open rectangle walk's restricted trace contains only original
edges that are open in the supplied configuration. -/
theorem rectangle_open_walk_trace_subset (a : LatticeVertex) (w h : ℕ)
    (A : Configuration (rectangleGraph a w h)) {u v : RectangleVertex a w h}
    (p : (openGraph (rectangleGraph a w h) A).Walk u v) :
    rectangleTraceConfiguration a w h (p.map (rectangleOpenGraphToSquare a w h A)) ⊆ A := by
  intro e he
  have hm := (mem_rectangleTraceConfiguration a w h _ e).mp he
  rw [SimpleGraph.Walk.edges_map] at hm
  obtain ⟨f,hf,hfe⟩ := List.mem_map.mp hm
  have hfe' : f = e.val := (Sym2.map.injective Subtype.val_injective) hfe
  rw [hfe'] at hf
  have hopen := p.edges_subset_edgeSet hf
  rw [openGraph_edgeSet] at hopen
  obtain ⟨g,hg,hge⟩ := hopen
  have hge' : g = e := Subtype.ext hge
  simpa only [hge',Finset.mem_coe] using hg

/-- Complementary dual interpolation, even after projection, is disjoint from
any original lattice walk whose rectangle trace is open in the configuration. -/
theorem clamped_dualCurve_disjoint_of_trace_subset (a : LatticeVertex) (w h : ℕ)
    (A : Configuration (rectangleGraph a w h))
    {x y : LatticeVertex} (p : PD.squareLattice.Walk x y)
    (hp : rectangleTraceConfiguration a w h p ⊆ A)
    {u v : RectangleDualVertex a w h}
    (q : (openGraph (rectangleDualGraph a w h)
      (rectangleDualConfiguration a w h A)).Walk u v) (hq : 0 < q.length) :
    Disjoint (Set.range (latticeWalkPath unitLatticeMesh p))
      (Set.range (clampedRectangleDualCurve a w h A q)) := by
  apply Set.disjoint_left.mpr
  rintro z hzP ⟨θ,rfl⟩
  let Q := q.map (rectangleDualOpenGraphToSquare a w h (rectangleDualConfiguration a w h A))
  obtain ⟨d,hd,hzD⟩ := rectangleDualWalkPath_point_on_dualBond unitLatticeMesh
    a w h A q (by simpa only [SimpleGraph.Walk.length_map] using hq)
    (show dualWalkCurve unitLatticeMesh Q θ ∈ Set.range (dualWalkCurve unitLatticeMesh Q)
      from ⟨θ,rfl⟩)
  have hd' : d.primalEdge ∉ rectangleTraceConfiguration a w h p := fun hm => hd (hp hm)
  exact Set.disjoint_left.mp (trace_closed_dualBond_disjoint_walk unitLatticeMesh
    a w h p d hd') hzP (rectangleClamp_dualBond_mem a w h d hzD)

end
end PottsContinuity.PlanarTopology
