-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `Medial/CycleComplementaryPathInside.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.Medial.CycleComplementaryPath
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.FKC.Medial

open SimpleGraph

/-- If a simple path is contained in a simple cycle and every cycle vertex
outside `K` is on that path, then the cycle has a complementary simple path
whose support stays in `K`. The only overlap between the two paths is derived
from the actual appended `IsCycle` conclusion. -/
theorem exists_complementary_path_support_subset
    {V : Type*} {G : SimpleGraph V} {a b z : V}
    (hab : a ≠ b) (c : G.Walk z z) (hc : c.IsCycle)
    (r : G.Walk a b) (hr : r.IsPath)
    (hrc : ∀ e, e ∈ r.edges → e ∈ c.edges)
    (K : Set V) (haK : a ∈ K) (hbK : b ∈ K)
    (houtside : ∀ v, v ∈ c.support → v ∉ K → v ∈ r.support) :
    ∃ s : G.Walk b a, s.IsPath ∧ (∀ x ∈ s.support, x ∈ K) ∧
      List.Disjoint r.edges s.edges ∧
      (∀ e, e ∈ c.edges → e ∈ r.edges ∨ e ∈ s.edges) ∧
      (∀ e, e ∈ r.edges ∨ e ∈ s.edges → e ∈ c.edges) ∧
      (r.append s).IsCycle := by
  classical
  have hrne : ¬ r.Nil := Walk.not_nil_of_ne hab
  have haR : a ∈ r.support := r.start_mem_support
  have haC : a ∈ c.support := by
    obtain ⟨e, he, hae⟩ :=
      (r.mem_support_iff_exists_mem_edges_of_not_nil hrne).mp haR
    exact (c.mem_support_iff_exists_mem_edges).mpr
      (Or.inr ⟨e, hrc e he, hae⟩)
  have hbR : b ∈ r.support := r.end_mem_support
  have hbC : b ∈ c.support := by
    obtain ⟨e, he, hbe⟩ :=
      (r.mem_support_iff_exists_mem_edges_of_not_nil hrne).mp hbR
    exact (c.mem_support_iff_exists_mem_edges).mpr
      (Or.inr ⟨e, hrc e he, hbe⟩)
  let c' : G.Walk a a := c.rotate a haC
  have hc' : c'.IsCycle := hc.rotate haC
  have hrotateEdges : c'.edges ~r c.edges := Walk.rotate_edges c a haC
  have hrotateSupport : ∀ x, x ∈ c'.support ↔ x ∈ c.support := by
    intro x
    exact Walk.mem_support_rotate_iff c a haC
  have hrc' : ∀ e, e ∈ r.edges → e ∈ c'.edges := by
    intro e he
    exact hrotateEdges.perm.mem_iff.mpr (hrc e he)
  obtain ⟨s, hsPath, hdisj, hcover', hback, hsCycle⟩ :=
    exists_complementary_path hab c' hc' r hr hrc'
  have hsne : ¬ s.Nil := Walk.not_nil_of_ne hab.symm
  have hsSupportCycle : ∀ x ∈ s.support, x ∈ c'.support := by
    intro x hx
    obtain ⟨e, he, hxe⟩ :=
      (s.mem_support_iff_exists_mem_edges_of_not_nil hsne).mp hx
    have heCycle : e ∈ c'.edges := hback e (Or.inr he)
    exact (c'.mem_support_iff_exists_mem_edges).mpr (Or.inr ⟨e, heCycle, hxe⟩)
  have hdisjSupportTail : List.Disjoint r.support.tail s.support.tail := by
    have hnodup : (r.append s).support.tail.Nodup := hsCycle.support_nodup
    rw [Walk.tail_support_append] at hnodup
    exact (List.nodup_append'.mp hnodup).2.2
  have hsK : ∀ x ∈ s.support, x ∈ K := by
    intro x hx
    by_contra hxK
    have hxC' : x ∈ c'.support := hsSupportCycle x hx
    have hxC : x ∈ c.support := (hrotateSupport x).mp hxC'
    have hxR : x ∈ r.support := houtside x hxC hxK
    have hxa : x ≠ a := by
      intro h
      subst x
      exact hxK haK
    have hxb : x ≠ b := by
      intro h
      subst x
      exact hxK hbK
    have hxRtail : x ∈ r.support.tail := by
      rw [← r.cons_tail_support] at hxR
      simp only [List.mem_cons] at hxR
      rcases hxR with h | h
      · exact (hxa h).elim
      · exact h
    have hxStail : x ∈ s.support.tail := by
      rw [← s.cons_tail_support] at hx
      simp only [List.mem_cons] at hx
      rcases hx with h | h
      · exact (hxb h).elim
      · exact h
    exact (List.disjoint_left.mp hdisjSupportTail hxRtail hxStail)
  refine ⟨s, hsPath, hsK, hdisj, ?_, ?_, hsCycle⟩
  · intro e he
    have he' : e ∈ c'.edges := hrotateEdges.perm.mem_iff.mpr he
    exact hcover' e he'
  · intro e he
    exact hrotateEdges.perm.mem_iff.mp (hback e he)

end PottsContinuity.FKC.Medial
