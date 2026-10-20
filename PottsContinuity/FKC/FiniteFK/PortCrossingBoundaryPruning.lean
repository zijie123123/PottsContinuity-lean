-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/PortCrossingBoundaryPruning.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.ActualConnectionFirstHitPath
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.FKC.FiniteFK

/-- A simple path with only its first vertex in `S` and only its last vertex
in `T` survives after deleting edges internal to either terminal set. -/
private theorem path_transfer_of_terminal_simple
    {V : Type*} [DecidableEq V] {G H : SimpleGraph V} {S T : Set V}
    {x y : V} (p : G.Walk x y) (hp : p.IsPath)
    (hS : ∀ z ∈ p.support, z ∈ S → z = x)
    (hT : ∀ z ∈ p.support, z ∈ T → z = y)
    (hretain : ∀ {u v}, G.Adj u v → ¬ (u ∈ S ∧ v ∈ S) →
      ¬ (u ∈ T ∧ v ∈ T) → H.Adj u v) :
    Nonempty (H.Walk x y) := by
  induction p with
  | nil =>
      exact ⟨SimpleGraph.Walk.nil⟩
  | @cons x z y hadj tail ih =>
      have hp' := hp
      have hnodup := hp.support_nodup
      simp only [SimpleGraph.Walk.support_cons, List.nodup_cons] at hnodup
      have hxP : x ∈ (SimpleGraph.Walk.cons hadj tail).support := by simp
      have hzP : z ∈ (SimpleGraph.Walk.cons hadj tail).support := by simp
      have hnotS : ¬ (x ∈ S ∧ z ∈ S) := by
        rintro ⟨hxS, hzS⟩
        have hxEq := hS x hxP hxS
        have hzEq := hS z hzP hzS
        exact (G.ne_of_adj hadj) (hxEq.trans hzEq.symm)
      have hnotT : ¬ (x ∈ T ∧ z ∈ T) := by
        rintro ⟨hxT, hzT⟩
        have hxEq := hT x hxP hxT
        have hzEq := hT z hzP hzT
        exact (G.ne_of_adj hadj) (hxEq.trans hzEq.symm)
      have hadjH : H.Adj x z := hretain hadj hnotS hnotT
      have htailPath : tail.IsPath := by simpa using hp.tail
      have htailS : ∀ w ∈ tail.support, w ∈ S → w = z := by
        intro w hw hwS
        have hwP : w ∈ (SimpleGraph.Walk.cons hadj tail).support := by
          simp [hw]
        have hwEq := hS w hwP hwS
        have hxNotTail := hnodup.1
        have hxIn : x ∈ tail.support := by simpa [hwEq] using hw
        exact (hxNotTail hxIn).elim
      have htailT : ∀ w ∈ tail.support, w ∈ T → w = y := by
        intro w hw hwT
        have hwP : w ∈ (SimpleGraph.Walk.cons hadj tail).support := by
          simp [hw]
        exact hT w hwP hwT
      obtain ⟨tailH⟩ := ih htailPath htailS htailT
      exact ⟨SimpleGraph.Walk.cons hadjH tailH⟩

/-- Between two terminal sets, connectivity is unchanged when every edge
internal to either terminal set is removed. The path is trimmed to its first
hit of `T` and then to its last hit of `S` before transferring it. -/
theorem reachable_between_sets_iff_of_retain_edges
    {V : Type*} [DecidableEq V] {G H : SimpleGraph V} {S T : Set V}
    (hHG : H ≤ G)
    (hretain : ∀ {u v}, G.Adj u v → ¬ (u ∈ S ∧ v ∈ S) →
      ¬ (u ∈ T ∧ v ∈ T) → H.Adj u v) :
    (∃ x ∈ S, ∃ y ∈ T, G.Reachable x y) ↔
      (∃ x ∈ S, ∃ y ∈ T, H.Reachable x y) := by
  classical
  constructor
  · rintro ⟨x, hxS, y, hyT, hxy⟩
    obtain ⟨p, hp⟩ := hxy.exists_isPath
    obtain ⟨t, htT, q, hq, hqSub, hTfirst⟩ :=
      walk_exists_first_hit_prefix p hyT hp
    obtain ⟨s, hsS, r, hr, hrSub, hSfirst⟩ :=
      walk_exists_first_hit_prefix q.reverse hxS hq.reverse
    have hsupportRtoQ : ∀ z ∈ r.support, z ∈ q.support := by
      intro z hz
      have hz' := hrSub z hz
      simpa only [SimpleGraph.Walk.support_reverse, List.mem_reverse] using hz'
    have hrS : ∀ z ∈ r.support, z ∈ S → z = s := hSfirst
    have hrT : ∀ z ∈ r.support, z ∈ T → z = t := by
      intro z hz hzT
      exact hTfirst z (hsupportRtoQ z hz) hzT
    have htrimmed := path_transfer_of_terminal_simple r.reverse hr.reverse
      (by
        intro z hz hzS
        have hzR : z ∈ r.support := by
          simpa only [SimpleGraph.Walk.support_reverse, List.mem_reverse] using hz
        exact hrS z hzR hzS)
      (by
        intro z hz hzT
        have hzR : z ∈ r.support := by
          simpa only [SimpleGraph.Walk.support_reverse, List.mem_reverse] using hz
        exact hrT z hzR hzT)
      hretain
    rcases htrimmed with ⟨pH⟩
    exact ⟨s, hsS, t, htT, pH.reachable⟩
  · rintro ⟨x, hxS, y, hyT, hxy⟩
    obtain ⟨p⟩ := hxy
    exact ⟨x, hxS, y, hyT, (p.mapLe hHG).reachable⟩

end PottsContinuity.FKC.FiniteFK

