module

public import PottsContinuity.PlanarTopology.SubpathExtraction

@[expose] public section

namespace PottsContinuity.PlanarTopology

/-- Between two vertex sets, clip an original walk to a contiguous segment
whose only visits to those sets are at its corresponding endpoints. -/
theorem walk_subwalk_between_sets {V : Type*} {G : SimpleGraph V}
    {u v : V} (p : G.Walk u v) (B D : Set V) (hu : u ∈ B) (hv : v ∈ D) :
    ∃ x ∈ B, ∃ y ∈ D, ∃ q : G.Walk x y, q.IsSubwalk p ∧
      (∀ z ∈ q.support, z ∈ B → z = x) ∧
      (∀ z ∈ q.support, z ∈ D → z = y) := by
  obtain ⟨y,hy,r,s,hp,hr⟩ := walk_first_entry p D hv
  obtain ⟨x,hx,q,k,hrrev,hq⟩ := walk_first_entry r.reverse B hu
  have hr' : r = k.reverse.append q.reverse := by
    have h := congrArg SimpleGraph.Walk.reverse hrrev
    simpa only [SimpleGraph.Walk.reverse_reverse,SimpleGraph.Walk.reverse_append] using h
  have hqr : q.reverse.IsSubwalk r := SimpleGraph.Walk.isSubwalk_of_append_right hr'
  have hqp : q.reverse.IsSubwalk p := hqr.trans
    (SimpleGraph.Walk.isSubwalk_of_append_left hp)
  refine ⟨x,hx,y,hy,q.reverse,hqp,?_,?_⟩
  · intro z hz hzB
    apply hq z _ hzB
    simpa only [SimpleGraph.Walk.support_reverse,List.mem_reverse] using hz
  · intro z hz hzD
    exact hr z (hqr.support_subset hz) hzD

end PottsContinuity.PlanarTopology
