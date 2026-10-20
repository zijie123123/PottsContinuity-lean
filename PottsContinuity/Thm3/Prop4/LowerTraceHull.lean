module

public import PottsContinuity.PlanarTopology.ExteriorBottomExtension
public import PottsContinuity.Thm3.Prop4.MaximalExcursionSupportingLine

/-!
# The lower filled region of an arbitrary finite trace

Top access is tested by literal lattice walks inside the original box which
avoid the trace. Its complement lies below the trace in every column, including
boundary columns and degenerate boxes.
-/

@[expose] public section

namespace PottsContinuity.Thm3.Prop4
open PD.FK
noncomputable section

/-- Access to the top row inside the box without visiting the trace. -/
def traceTopAccessible (n : ℕ) (trace : Finset LatticeVertex) (z : LatticeVertex) : Prop :=
  ∃ t : LatticeVertex, t.2 = (n : ℤ) ∧
    ∃ p : PD.squareLattice.Walk z t, ∀ w ∈ p.support, w ∈ box n ∧ w ∉ trace

/-- The trace together with every box component cut off from the top row. -/
def lowerTraceHull (n : ℕ) (trace : Finset LatticeVertex) : Finset LatticeVertex :=
  by
    classical
    exact (box n).filter fun z => ¬traceTopAccessible n trace z

/-- Every vertex in the filled lower region lies below an actual trace vertex
in its own column. No path simplicity or choice of a maximal trace is needed. -/
theorem lowerTraceHull_column_witness (n : ℕ) (trace : Finset LatticeVertex)
    (z : LatticeVertex) (hz : z ∈ lowerTraceHull n trace) :
    ∃ w ∈ trace, z.1 = w.1 ∧ z.2 ≤ w.2 := by
  classical
  obtain ⟨hzB,hno⟩ := Finset.mem_filter.mp hz
  by_contra h
  have havoid : ∀ w : LatticeVertex, w.1 = z.1 → z.2 ≤ w.2 → w ∉ trace := by
    intro w hwx hwy hw
    exact h ⟨w,hw,hwx.symm,hwy⟩
  have hzcoord : -(n : ℤ) ≤ z.1 ∧ z.1 ≤ n ∧ -(n : ℤ) ≤ z.2 ∧ z.2 ≤ n := by
    simpa only [box,Finset.mem_product,Finset.mem_Icc,and_assoc] using hzB
  obtain ⟨p,hp⟩ := PlanarTopology.vertical_walk_between z.1 z.2 (n : ℤ)
  have hstart : (z.1,z.2) = z := Prod.eta z
  let p' := p.copy hstart rfl
  apply hno
  refine ⟨(z.1,n),rfl,p',?_⟩
  intro w hw
  have hw' : w ∈ p.support := by
    simpa only [p',SimpleGraph.Walk.support_copy] using hw
  have hh := hp w hw'
  have hy : z.2 ≤ w.2 ∧ w.2 ≤ n := by
    simpa only [min_eq_left hzcoord.2.2.2,max_eq_right hzcoord.2.2.2] using hh.2
  refine ⟨?_,havoid w hh.1 hy.1⟩
  simp only [box,Finset.mem_product,Finset.mem_Icc]
  exact ⟨⟨hh.1 ▸ hzcoord.1,hh.1 ▸ hzcoord.2.1⟩,⟨hzcoord.2.2.1.trans hy.1,hy.2⟩⟩

end
end PottsContinuity.Thm3.Prop4
