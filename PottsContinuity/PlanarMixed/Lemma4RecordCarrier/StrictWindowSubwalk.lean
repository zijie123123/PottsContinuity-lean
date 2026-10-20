module

public import PottsContinuity.PlanarTopology.SubpathExtraction

@[expose] public section

namespace PottsContinuity.PlanarMixed.Lemma4Connectors
open PlanarTopology

/-- Clip a slab crossing again at its first terminal-side and last initial-side
visit. No remaining edge lies entirely in either vertical boundary column. -/
theorem walk_subwalk_between_levels_no_boundary_edges
    {V : Type*} {G : SimpleGraph V} (f : V → ℤ)
    (hstep : ∀ x y, G.Adj x y → |f x-f y| ≤ 1)
    {u v : V} (p : G.Walk u v) {a b : ℤ}
    (hab : a < b) (hu : f u ≤ a) (hv : b ≤ f v) :
    ∃ x y, ∃ q : G.Walk x y, q.IsSubwalk p ∧ f x=a ∧ f y=b ∧
      (∀ z ∈ q.support, a ≤ f z ∧ f z ≤ b) ∧
      (∀ s t, s(s,t) ∈ q.edges → ¬ (f s=a ∧ f t=a) ∧ ¬ (f s=b ∧ f t=b)) := by
  classical
  obtain ⟨x₀,y₀,q₀,hq₀,hx₀,hy₀,hslab⟩ := walk_subwalk_between_levels f hstep p hab.le hu hv
  obtain ⟨y,hy,t,k,ht,hfirst⟩ := walk_first_entry q₀ {z | f z=b} hy₀
  obtain ⟨x,hx,r,s,hr,hlast⟩ := walk_first_entry t.reverse {z | f z=a} (by
    change f x₀=a
    exact hx₀)
  have hqt : r.reverse.IsSubwalk t := by
    have he := congrArg SimpleGraph.Walk.reverse hr
    have ht' : t=s.reverse.append r.reverse := by
      simpa only [SimpleGraph.Walk.reverse_reverse,SimpleGraph.Walk.reverse_append] using he
    exact SimpleGraph.Walk.isSubwalk_of_append_right ht'
  have htq : t.IsSubwalk q₀ := SimpleGraph.Walk.isSubwalk_of_append_left ht
  have hqp : r.reverse.IsSubwalk p := hqt.trans (htq.trans hq₀)
  refine ⟨x,y,r.reverse,hqp,hx,hy,?_,?_⟩
  · intro z hz
    exact hslab z (htq.support_subset (hqt.support_subset hz))
  · intro v w he
    have hv := r.reverse.fst_mem_support_of_mem_edges he
    have hw := r.reverse.snd_mem_support_of_mem_edges he
    have hv' : v ∈ r.support := by simpa only [SimpleGraph.Walk.support_reverse,List.mem_reverse] using hv
    have hw' : w ∈ r.support := by simpa only [SimpleGraph.Walk.support_reverse,List.mem_reverse] using hw
    constructor
    · rintro ⟨ha,hb⟩
      have hvx := hlast v hv' ha
      have hwx := hlast w hw' hb
      exact (r.reverse.adj_of_mem_edges he).ne (hvx.trans hwx.symm)
    · rintro ⟨ha,hb⟩
      have hvy := hfirst v (hqt.support_subset hv) ha
      have hwy := hfirst w (hqt.support_subset hw) hb
      exact (r.reverse.adj_of_mem_edges he).ne (hvy.trans hwy.symm)

end PottsContinuity.PlanarMixed.Lemma4Connectors
