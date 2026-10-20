module

public import PottsContinuity.Thm4Records.FullTraceClip

@[expose] public section

namespace PottsContinuity.Thm4Records

/-- The interior of a simple walk with nonadjacent endpoints is a nonempty
connected walk. Every original edge has an endpoint in this interior. -/
theorem path_interior_covers_edges {V : Type*} {G : SimpleGraph V}
    {u v : V} (q : G.Walk u v) (hp : q.IsPath) (hne : u ≠ v)
    (hnot : ¬ G.Adj u v) :
    ∃ a b, ∃ r : G.Walk a b,
      q.support=u :: (r.support ++ [v]) ∧
      u ∉ r.support ∧ v ∉ r.support ∧
      (∀ x y, s(x,y) ∈ q.edges → x ∈ r.support ∨ y ∈ r.support) := by
  cases q with
  | nil => exact (hne rfl).elim
  | @cons u a v h tail =>
    have ht : ¬ tail.Nil := by
      intro hn
      cases hn
      exact hnot h
    let r := tail.dropLast
    have hs : (tail.cons h).support=u :: (r.support ++ [v]) := by
      rw [SimpleGraph.Walk.support_cons,← SimpleGraph.Walk.support_dropLast_concat ht]
    have hnodup : (u :: (r.support ++ [v])).Nodup := hs ▸ hp.support_nodup
    have hu : u ∉ r.support := by
      have hh := (List.nodup_cons.mp hnodup).1
      exact fun hh' => hh (List.mem_append_left _ hh')
    have hv : v ∉ r.support := by
      have hh := (List.nodup_append.mp (List.nodup_cons.mp hnodup).2).2.2
      exact fun hh' => hh v hh' v (by simp) rfl
    refine ⟨a,tail.penultimate,r,hs,hu,hv,?_⟩
    intro x y he
    by_contra hn
    have hn' : x ∉ r.support ∧ y ∉ r.support := by tauto
    have hx := SimpleGraph.Walk.mem_support_of_mem_edges he (Sym2.mem_mk_left _ _)
    have hy := SimpleGraph.Walk.mem_support_of_mem_edges he (Sym2.mem_mk_right _ _)
    rw [hs] at hx hy
    simp only [List.mem_cons,List.mem_append,List.not_mem_nil,or_false,hn'.1,hn'.2,false_or] at hx hy
    have hadj : G.Adj x y := G.mem_edgeSet.mp ((tail.cons h).edges_subset_edgeSet he)
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · exact G.loopless.irrefl _ hadj
    · exact hnot hadj
    · exact hnot hadj.symm
    · exact G.loopless.irrefl _ hadj

/-- Extract a simple between-trace path together with its connected trace-free
interior. Every edge touches the interior when the two traces have no adjacent
vertices. All full trace vertices, including excursions, participate. -/
theorem walk_between_full_traces_with_interior
    {V : Type*} {G : SimpleGraph V} (L R : Set V)
    (hdisjoint : Disjoint L R)
    (hnot : ∀ u ∈ L, ∀ v ∈ R, ¬ G.Adj u v)
    {a b : V} (p : G.Walk a b) (ha : a ∈ L) (hb : b ∈ R) :
    ∃ u ∈ L, ∃ v ∈ R, ∃ q : G.Walk u v, ∃ c d, ∃ r : G.Walk c d,
      q.IsPath ∧ q.support ⊆ p.support ∧ q.edges ⊆ p.edges ∧
      q.support=u :: (r.support ++ [v]) ∧
      (∀ z ∈ r.support, z ∉ L ∧ z ∉ R) ∧
      (∀ x y, s(x,y) ∈ q.edges → x ∈ r.support ∨ y ∈ r.support) := by
  classical
  obtain ⟨u,hu,v,hv,q,hqp,hL,hR⟩ := walk_between_full_trace_contacts L R p ha hb
  let Q : G.Walk u v := q.toPath.val
  have hQsupport : Q.support ⊆ q.support := q.support_toPath_subset_support
  have hne : u ≠ v := by
    intro h
    exact Set.disjoint_left.mp hdisjoint hu (h ▸ hv)
  obtain ⟨c,d,r,hs,hui,hvi,hcover⟩ :=
    path_interior_covers_edges Q q.toPath.property hne (hnot u hu v hv)
  refine ⟨u,hu,v,hv,Q,c,d,r,q.toPath.property,(fun _ hz => hqp.support_subset (hQsupport hz)),
    (fun _ he => hqp.edges_subset (q.edges_toPath_subset_edges he)),hs,?_,hcover⟩
  intro z hz
  have hzQ : z ∈ Q.support := by rw [hs]; simp [hz]
  exact ⟨fun hzL => hui (hL z (hQsupport hzQ) hzL ▸ hz),
    fun hzR => hvi (hR z (hQsupport hzQ) hzR ▸ hz)⟩

end PottsContinuity.Thm4Records
