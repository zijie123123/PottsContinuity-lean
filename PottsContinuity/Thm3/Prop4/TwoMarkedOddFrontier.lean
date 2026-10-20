module

public import Mathlib.Combinatorics.SimpleGraph.DegreeSum
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-! # Two prescribed odd frontier vertices lie in one component -/

@[expose] public section

namespace PottsContinuity.Thm3.Prop4
noncomputable section

/-- A finite frontier with only two possible odd-degree vertices joins them
as soon as the first has odd degree. No cycle or simplicity restriction is needed. -/
theorem reachable_of_two_marked_odd_vertices {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (u v : V)
    (hu : Odd (G.degree u))
    (hodd : ∀ x : V, Odd (G.degree x) → x = u ∨ x = v) : G.Reachable u v := by
  classical
  let S : Set V := {x | G.Reachable u x}
  let u' : S := ⟨u,SimpleGraph.Reachable.refl u⟩
  have degrees (x : S) : (G.induce S).degree x = G.degree x.val := by
    apply SimpleGraph.degree_induce_of_neighborSet_subset
    intro y hxy
    exact x.property.trans hxy.reachable
  obtain ⟨x,hxu,hxodd⟩ := (G.induce S).exists_ne_odd_degree_of_exists_odd_degree u'
    (by rw [degrees]; exact hu)
  have hx := hodd x.val (by rwa [degrees] at hxodd)
  rcases hx with hxu' | hxv
  · exact (hxu (Subtype.ext hxu')).elim
  · exact hxv ▸ x.property

end
end PottsContinuity.Thm3.Prop4
