module

public import PottsContinuity.PlanarTopology.SubpathExtraction

@[expose] public section

namespace PottsContinuity.Push

/-- Truncate an actual walk at its FIRST visit to a lower integer level.
The only prefix vertex at or below that level is its terminal vertex. Thus
no edge along a spurious lower port row is retained by the truncation. -/
theorem walk_first_arrival_down {V : Type*} {G : SimpleGraph V}
    (f : V → ℤ) (hstep : ∀ x y, G.Adj x y → |f x-f y| ≤ 1)
    {u v : V} (p : G.Walk u v) (b : ℤ) (hu : b < f u) (hv : f v ≤ b) :
    ∃ z, ∃ (r : G.Walk u z) (s : G.Walk z v),
      f z=b ∧ p=r.append s ∧ ∀ x ∈ r.support, f x ≤ b → x=z := by
  induction p with
  | nil => omega
  | @cons u t v hut p ih =>
    by_cases ht : f t ≤ b
    · have htb : f t=b := by
        have hd := abs_le.mp (hstep u t hut)
        omega
      refine ⟨t,.cons hut .nil,p,htb,rfl,?_⟩
      intro x hx hxb
      have hx' : x=u ∨ x=t := by simpa only [SimpleGraph.Walk.support_cons,
        SimpleGraph.Walk.support_nil,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] using hx
      rcases hx' with rfl | rfl
      · omega
      · rfl
    · obtain ⟨z,r,s,hz,hp,hr⟩ := ih (by omega) hv
      refine ⟨z,r.cons hut,s,hz,?_,?_⟩
      · rw [hp]
        rfl
      · intro x hx hxb
        rcases List.mem_cons.mp hx with rfl | hx
        · omega
        · exact hr x hx hxb

end PottsContinuity.Push
