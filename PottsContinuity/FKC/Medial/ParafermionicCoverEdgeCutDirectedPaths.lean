-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `Medial/ParafermionicCoverEdgeCutDirectedPaths.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.Medial.ParafermionicCoverEdgeCutOrientation
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.FKC.FiniteFK

open PottsContinuity.FKC.Medial
open SimpleGraph
noncomputable section

 def edgeCutWalkDirected (n : ℕ) (hn : 1 ≤ n)
    (A : Configuration (ParafermionicAmbientGraph n))
    (e : (ParafermionicAmbientGraph n).edgeSet)
    (R : (ParafermionicCoverFinitePort n × Bool) →
      (ParafermionicCoverFinitePort n × Bool) → Prop) :
    {u v : ParafermionicCoverFinitePort n × Bool} →
      (parafermionicCoverFiniteEdgeCutGraph n hn A e).Walk u v → Prop
  | _, _, .nil => True
  | _, _, .cons (u := u) (v := v) _ p =>
      R u v ∧ edgeCutWalkDirected n hn A e R p

private theorem edgeCutWalkDirected_of_incoming
    (n : ℕ) (hn : 1 ≤ n) (A : Configuration (ParafermionicAmbientGraph n))
    (e : (ParafermionicAmbientGraph n).edgeSet)
    (R : (ParafermionicCoverFinitePort n × Bool) →
      (ParafermionicCoverFinitePort n × Bool) → Prop)
    (hchoose : ∀ {u v},
      (parafermionicCoverFiniteEdgeCutGraph n hn A e).Adj u v → R u v ∨ R v u)
    (hpred : ∀ {u v w}, R u w → R v w → u = v)
    {a b t : ParafermionicCoverFinitePort n × Bool}
    (p : (parafermionicCoverFiniteEdgeCutGraph n hn A e).Walk b t)
    (hp : p.IsPath) (hab : R a b) (ha : a ∉ p.support) :
    edgeCutWalkDirected n hn A e R p := by
  revert a hab ha hp
  induction p with
  | nil =>
      intro a hp hab ha
      trivial
  | @cons b c t hbc tail ih =>
      intro a hp hab ha
      have hbcR : R b c := by
        rcases hchoose hbc with h | h
        · exact h
        · have hac := hpred hab h
          have hc : c ∈ (SimpleGraph.Walk.cons hbc tail).support := by
            simp [SimpleGraph.Walk.support_cons]
          exact (ha (hac.symm ▸ hc)).elim
      have hbNotTail : b ∉ tail.support := by
        have hnodup := hp.support_nodup
        rw [SimpleGraph.Walk.support_cons] at hnodup
        exact (List.nodup_cons.mp hnodup).1
      exact ⟨hbcR, ih (SimpleGraph.Walk.IsPath.of_cons hp) hbcR hbNotTail⟩

private theorem edgeCutWalkDirected_of_no_incoming
    (n : ℕ) (hn : 1 ≤ n) (A : Configuration (ParafermionicAmbientGraph n))
    (e : (ParafermionicAmbientGraph n).edgeSet)
    (R : (ParafermionicCoverFinitePort n × Bool) →
      (ParafermionicCoverFinitePort n × Bool) → Prop)
    (hchoose : ∀ {u v},
      (parafermionicCoverFiniteEdgeCutGraph n hn A e).Adj u v → R u v ∨ R v u)
    (hpred : ∀ {u v w}, R u w → R v w → u = v)
    {s t : ParafermionicCoverFinitePort n × Bool}
    (p : (parafermionicCoverFiniteEdgeCutGraph n hn A e).Walk s t)
    (hp : p.IsPath)
    (hno : ∀ u, ¬ R u s) :
    edgeCutWalkDirected n hn A e R p := by
  cases p with
  | nil => trivial
  | cons hxy tail =>
      rename_i c
      have hxyR : R s c := by
        rcases hchoose hxy with h | h
        · exact h
        · exact (hno c h).elim
      have htailPath := SimpleGraph.Walk.IsPath.of_cons hp
      have hsNotTail : s ∉ tail.support := by
        have hnodup := hp.support_nodup
        rw [SimpleGraph.Walk.support_cons] at hnodup
        exact (List.nodup_cons.mp hnodup).1
      exact ⟨hxyR, edgeCutWalkDirected_of_incoming n hn A e R hchoose hpred
        tail htailPath hxyR hsNotTail⟩

private theorem edgeCutWalkDirected_last
    (n : ℕ) (hn : 1 ≤ n) (A : Configuration (ParafermionicAmbientGraph n))
    (e : (ParafermionicAmbientGraph n).edgeSet)
    (R : (ParafermionicCoverFinitePort n × Bool) →
      (ParafermionicCoverFinitePort n × Bool) → Prop)
    {s t : ParafermionicCoverFinitePort n × Bool}
    (p : (parafermionicCoverFiniteEdgeCutGraph n hn A e).Walk s t)
    (hp : edgeCutWalkDirected n hn A e R p) (hne : p.length ≠ 0) :
    ∃ u, R u t := by
  induction p with
  | nil => exact False.elim (hne rfl)
  | @cons a b t hab tail ih =>
      rcases hp with ⟨habR, htailR⟩
      cases tail with
      | nil => exact ⟨a, habR⟩
      | @cons b c t hbc rest =>
          exact ih htailR (by simp)

 def parafermionicCoverFiniteEdgeCutBackward (n : ℕ) (hn : 1 ≤ n)
    (A : Configuration (ParafermionicAmbientGraph n))
    (e : (ParafermionicAmbientGraph n).edgeSet)
    (u v : ParafermionicCoverFinitePort n × Bool) : Prop :=
  parafermionicCoverFiniteEdgeCutForward n hn A e v u

private theorem edgeCutBackward_adj_or (n : ℕ) (hn : 1 ≤ n)
    (A : Configuration (ParafermionicAmbientGraph n))
    (e : (ParafermionicAmbientGraph n).edgeSet)
    {u v : ParafermionicCoverFinitePort n × Bool}
    (h : (parafermionicCoverFiniteEdgeCutGraph n hn A e).Adj u v) :
    parafermionicCoverFiniteEdgeCutBackward n hn A e u v ∨
      parafermionicCoverFiniteEdgeCutBackward n hn A e v u := by
  rcases parafermionicCoverFiniteEdgeCut_adj_or_forward n hn A e h with h | h
  · exact Or.inr h
  · exact Or.inl h

private theorem edgeCutBackward_predecessor_unique (n : ℕ) (hn : 1 ≤ n)
    (A : Configuration (ParafermionicAmbientGraph n))
    (e : (ParafermionicAmbientGraph n).edgeSet)
    {u v w : ParafermionicCoverFinitePort n × Bool}
    (huw : parafermionicCoverFiniteEdgeCutBackward n hn A e u w)
    (hvw : parafermionicCoverFiniteEdgeCutBackward n hn A e v w) : u = v := by
  exact parafermionicCoverFiniteEdgeCutForward_successor_unique n hn A e huw hvw

theorem parafermionicCoverFiniteEdgeCutPartner_source_iff_not_source
    (n : ℕ) (hn : 1 ≤ n) (A : Configuration (ParafermionicAmbientGraph n))
    (e : (ParafermionicAmbientGraph n).edgeSet)
    (s : ParafermionicCoverFiniteEdgeCutTerminal n hn e) :
    parafermionicCoverFiniteEdgeCutSource n hn e
        (parafermionicCoverFiniteEdgeCutPartner n hn A e s) ↔
      ¬ parafermionicCoverFiniteEdgeCutSource n hn e s := by
  let t := parafermionicCoverFiniteEdgeCutPartner n hn A e s
  have hspec := parafermionicCoverFiniteEdgeCutPartner_spec n hn A e s
  have hne : s.1 ≠ t.1 := by
    intro h
    exact hspec.1 (Subtype.ext h.symm)
  have hreach :
      (parafermionicCoverFiniteEdgeCutGraph n hn A e).Reachable s.1 t.1 := by
    simpa [t] using hspec.2
  obtain ⟨p, hp⟩ := hreach.exists_isPath
  have hlen : 0 < p.length := by
    by_contra hz
    exact hne (p.eq_of_length_eq_zero (Nat.eq_zero_of_not_pos hz))
  have hpne : p.length ≠ 0 := Nat.ne_of_gt hlen
  have hsource_to_sink : parafermionicCoverFiniteEdgeCutSource n hn e s →
      ¬ parafermionicCoverFiniteEdgeCutSource n hn e t := by
    intro hs
    have hno : ∀ u, ¬ parafermionicCoverFiniteEdgeCutForward n hn A e u s.1 := by
      intro u h
      have hadj : (parafermionicCoverFiniteEdgeCutGraph n hn A e).Adj s.1 u := h.1.symm
      have hrev := parafermionicCoverFiniteEdgeCutTerminal_reverse_iff_not_source
        n hn A e s hadj
      exact (hrev.mp h) hs
    have hforward := edgeCutWalkDirected_of_no_incoming n hn A e
      (parafermionicCoverFiniteEdgeCutForward n hn A e)
      (by
        intro u v hadj
        exact parafermionicCoverFiniteEdgeCut_adj_or_forward n hn A e hadj)
      (by
        intro u v w huv hvw
        exact parafermionicCoverFiniteEdgeCutForward_predecessor_unique n hn A e huv hvw)
      p hp hno
    obtain ⟨u, hu⟩ := edgeCutWalkDirected_last n hn A e
      (parafermionicCoverFiniteEdgeCutForward n hn A e) p hforward hpne
    have hadj : (parafermionicCoverFiniteEdgeCutGraph n hn A e).Adj t.1 u := hu.1.symm
    have hrev := parafermionicCoverFiniteEdgeCutTerminal_reverse_iff_not_source
      n hn A e t hadj
    exact hrev.mp hu
  have hsink_to_source : ¬ parafermionicCoverFiniteEdgeCutSource n hn e s →
      parafermionicCoverFiniteEdgeCutSource n hn e t := by
    intro hns
    have hno : ∀ u, ¬ parafermionicCoverFiniteEdgeCutBackward n hn A e u s.1 := by
      intro u h
      change parafermionicCoverFiniteEdgeCutForward n hn A e s.1 u at h
      have hout := parafermionicCoverFiniteEdgeCutTerminal_forward_iff_source
        n hn A e s h.1
      exact hns (hout.mp h)
    have hbackward := edgeCutWalkDirected_of_no_incoming n hn A e
      (parafermionicCoverFiniteEdgeCutBackward n hn A e)
      (edgeCutBackward_adj_or n hn A e)
      (edgeCutBackward_predecessor_unique n hn A e)
      p hp hno
    obtain ⟨u, hu⟩ := edgeCutWalkDirected_last n hn A e
      (parafermionicCoverFiniteEdgeCutBackward n hn A e) p hbackward hpne
    change parafermionicCoverFiniteEdgeCutForward n hn A e t.1 u at hu
    have hout := parafermionicCoverFiniteEdgeCutTerminal_forward_iff_source
      n hn A e t hu.1
    exact hout.mp hu

  constructor
  · intro ht hs
    exact (hsource_to_sink hs) ht
  · exact hsink_to_source

end
end PottsContinuity.FKC.FiniteFK
