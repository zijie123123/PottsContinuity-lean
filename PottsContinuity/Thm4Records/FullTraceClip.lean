module

public import PottsContinuity.PlanarTopology.SubpathExtraction
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

@[expose] public section

namespace PottsContinuity.Thm4Records
open PlanarTopology

/-- Clip between the last left-trace contact before the first right-trace
contact. Both traces are arbitrary full sets; disconnected excursions are kept. -/
theorem walk_between_full_trace_contacts
    {V : Type*} {G : SimpleGraph V} (L R : Set V)
    {a b : V} (p : G.Walk a b) (ha : a ∈ L) (hb : b ∈ R) :
    ∃ u ∈ L, ∃ v ∈ R, ∃ q : G.Walk u v,
      q.IsSubwalk p ∧
      (∀ z ∈ q.support, z ∈ L → z=u) ∧
      (∀ z ∈ q.support, z ∈ R → z=v) := by
  obtain ⟨v,hv,t,k,ht,hfirst⟩ := walk_first_entry p R hb
  obtain ⟨u,hu,r,s,hr,hlast⟩ := walk_first_entry t.reverse L ha
  have hqt : r.reverse.IsSubwalk t := by
    have he := congrArg SimpleGraph.Walk.reverse hr
    have ht' : t=s.reverse.append r.reverse := by
      simpa only [SimpleGraph.Walk.reverse_reverse,SimpleGraph.Walk.reverse_append] using he
    exact SimpleGraph.Walk.isSubwalk_of_append_right ht'
  have htp : t.IsSubwalk p := SimpleGraph.Walk.isSubwalk_of_append_left ht
  refine ⟨u,hu,v,hv,r.reverse,hqt.trans htp,?_,?_⟩
  · intro z hz hzL
    exact hlast z (by simpa only [SimpleGraph.Walk.support_reverse,List.mem_reverse] using hz) hzL
  · intro z hz hzR
    exact hfirst z (hqt.support_subset hz) hzR

/-- Once the original edge states on the clipped segment are verified, its
connectivity is genuine. Neither trace is replaced by a selected square crop. -/
theorem actual_connection_of_full_trace_segment
    {V : Type*} {G H : SimpleGraph V} (L R : Set V)
    {u v : V} (q : G.Walk u v) (hu : u ∈ L) (hv : v ∈ R)
    (hedges : ∀ x y, s(x,y) ∈ q.edges → H.Adj x y) :
    ∃ u ∈ L, ∃ v ∈ R, H.Reachable u v := by
  have hwalk : ∀ {a b : V} (p : G.Walk a b),
      (∀ x y, s(x,y) ∈ p.edges → H.Adj x y) → H.Reachable a b := by
    intro a b p
    induction p with
    | nil => intro _; exact SimpleGraph.Reachable.refl _
    | @cons a b c hab p ih =>
      intro hp
      exact (hp a b (by simp)).reachable.trans
        (ih (fun x y hxy => hp x y (by simp [hxy])))
  exact ⟨u,hu,v,hv,hwalk q hedges⟩

end PottsContinuity.Thm4Records
