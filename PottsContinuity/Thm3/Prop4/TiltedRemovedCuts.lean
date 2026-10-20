module

public import PottsContinuity.Thm3.Prop4.TiltedInterval

/-! # Every tested exterior cut is among the removed interval edges -/

@[expose] public section

namespace PottsContinuity.Thm3.Prop4

noncomputable section

/-- Endpoints of a mapped inner edge lie in the actual vertex embedding range. -/
theorem endpoint_mem_range_of_mapped_edge {V U : Type*} (G : SimpleGraph U) (f : U ↪ V)
    (e : Sym2 V) (he : e ∈ (G.map f).edgeSet) (v : V) (hv : v ∈ e) :
    v ∈ Set.range f := by
  rw [SimpleGraph.edgeSet_map] at he
  obtain ⟨d,_,hde⟩ := he
  rw [← hde] at hv
  obtain ⟨u,_,hu⟩ := Sym2.mem_map.mp hv
  exact ⟨u,hu⟩

/-- A cut before the left endpoint or at/after the right endpoint contains
no edge internal to the selected interval. -/
theorem tiltedCutEdges_subset_intervalRemoved (n M : ℕ) (t : ℝ) (lo hi k : ℤ)
    (hk : k < lo ∨ hi ≤ k) :
    tiltedWindowCutEdges n M t k ⊆
      PD.FK.subgraphRemovedEdges
        ((squareLattice.induce (tiltedInterval n M t lo hi : Set (ℤ × ℤ))).map
          (tiltedIntervalEmbedding n M t lo hi))
        (squareLattice.induce (tiltedWindow n M t : Set (ℤ × ℤ))) := by
  classical
  intro e he
  apply (PD.FK.mem_subgraphRemovedEdges e).mpr
  intro hemap
  obtain ⟨y,hy⟩ := (Finset.mem_filter.mp he).2
  have hleft : (k,y) ∈ Sym2.map Subtype.val e.val := by rw [hy]; simp
  have hright : (k+1,y) ∈ Sym2.map Subtype.val e.val := by rw [hy]; simp
  rcases hk with hk | hk
  · obtain ⟨z,hz,hzval⟩ := Sym2.mem_map.mp hleft
    have hrange := endpoint_mem_range_of_mapped_edge _ (tiltedIntervalEmbedding n M t lo hi)
      e.val hemap z hz
    have hb := (mem_tiltedIntervalEmbedding_range n M t lo hi z).mp hrange
    have hx := congrArg Prod.fst hzval
    omega
  · obtain ⟨z,hz,hzval⟩ := Sym2.mem_map.mp hright
    have hrange := endpoint_mem_range_of_mapped_edge _ (tiltedIntervalEmbedding n M t lo hi)
      e.val hemap z hz
    have hb := (mem_tiltedIntervalEmbedding_range n M t lo hi z).mp hrange
    have hx := congrArg Prod.fst hzval
    omega

end

end PottsContinuity.Thm3.Prop4
