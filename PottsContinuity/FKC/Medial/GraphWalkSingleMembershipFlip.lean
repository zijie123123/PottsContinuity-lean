-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `Medial/GraphWalkSingleMembershipFlip.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import Mathlib.Combinatorics.SimpleGraph.Paths
public import Mathlib.Combinatorics.SimpleGraph.Walk.Traversal
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.FKC.Medial

open SimpleGraph

private theorem endpoint_iff_of_all_darts
    {V : Type*} {G : SimpleGraph V} {u v : V}
    (p : G.Walk u v) (F : V → Prop)
    (hstep : ∀ d ∈ p.darts, F d.fst ↔ F d.snd) : F u ↔ F v := by
  induction p with
  | nil => simp
  | @cons a b c hab tail ih =>
      have hfirst : F a ↔ F b := hstep ⟨(a, b), hab⟩ (by simp)
      have htail : ∀ d ∈ tail.darts, F d.fst ↔ F d.snd := by
        intro d hd
        exact hstep d (by simp [hd])
      exact hfirst.trans (ih htail)

/-- Along a simple graph path, a support vertex different from the start
forces endpoint disagreement when exactly its incoming step changes the predicate. -/
theorem graphWalk_endpoint_not_iff_of_unique_support_flip
    {V : Type*} {G : SimpleGraph V} {u v m : V}
    (p : G.Walk u v) (hp : p.IsPath) (hm : m ∈ p.support) (hmu : m ≠ u)
    (F : V → Prop)
    (hstep : ∀ d ∈ p.darts,
      ((F d.fst ↔ F d.snd) ↔ d.snd ≠ m)) :
    ¬ (F u ↔ F v) := by
  induction p with
  | nil =>
      simp only [Walk.support_nil, List.mem_singleton] at hm
      subst m
      exact (hmu rfl).elim
  | @cons a b c hab tail ih =>
      have hnodup := hp.support_nodup
      simp only [Walk.support_cons, List.nodup_cons] at hnodup
      have hstepHead := hstep ⟨(a, b), hab⟩ (by simp)
      by_cases hmb : m = b
      · have hflip : ¬ (F a ↔ F b) := by simpa [hmb] using hstepHead
        have htailMiss : ∀ d ∈ tail.darts, d.snd ≠ b := by
          intro d hd hdb
          have htailTail : tail.support.tail = tail.darts.map (fun d : G.Dart => d.toProd.2) := by
            exact (congrArg List.tail (Walk.cons_map_snd_darts tail)).symm
          have hdbmem : b ∈ tail.support.tail := by
            rw [htailTail]
            exact List.mem_map.mpr ⟨d, hd, hdb⟩
          have ht := hnodup.2
          rw [← Walk.cons_map_snd_darts tail] at ht
          simp only [List.nodup_cons] at ht
          exact ht.1 (by simpa [htailTail] using hdbmem)
        have htailAgreement : ∀ d ∈ tail.darts, F d.fst ↔ F d.snd := by
          intro d hd
          have hneq : d.snd ≠ m := by simpa [hmb] using htailMiss d hd
          exact (hstep d (by simp [hd])).mpr hneq
        have htailEnd := endpoint_iff_of_all_darts tail F htailAgreement
        intro huv
        exact hflip (huv.trans htailEnd.symm)
      · have hmTail : m ∈ tail.support := by
          simp only [Walk.support_cons, List.mem_cons] at hm
          rcases hm with hma | hmt
          · exact (hmu hma).elim
          · exact hmt
        have htailPath : tail.IsPath := by
          exact Walk.IsPath.mk' hnodup.2
        have htailNot := ih htailPath hmTail hmb (by
          intro d hd
          exact hstep d (by simp [hd]))
        have hagree : F a ↔ F b := (hstepHead).2 (fun h => hmb h.symm)
        intro huv
        exact htailNot (hagree.symm.trans huv)

/-- The source-oriented counterpart: a support vertex different from the
terminal point forces disagreement when exactly its outgoing step changes
the predicate. -/
theorem graphWalk_endpoint_not_iff_of_unique_support_source_flip
    {V : Type*} {G : SimpleGraph V} {u v m : V}
    (p : G.Walk u v) (hp : p.IsPath) (hm : m ∈ p.support) (hmv : m ≠ v)
    (F : V → Prop)
    (hstep : ∀ d ∈ p.darts,
      ((F d.fst ↔ F d.snd) ↔ d.fst ≠ m)) :
    ¬ (F u ↔ F v) := by
  have hm' : m ∈ p.reverse.support := by simpa using hm
  have hmv' : m ≠ v := hmv
  have hstep' : ∀ d ∈ p.reverse.darts,
      ((F d.fst ↔ F d.snd) ↔ d.snd ≠ m) := by
    intro d hd
    have hs := hstep d.symm (Walk.mem_darts_reverse.mp hd)
    simpa [Dart.symm, iff_comm] using hs
  have hnot := graphWalk_endpoint_not_iff_of_unique_support_flip
    p.reverse hp.reverse hm' hmv' F hstep'
  intro huv
  exact hnot huv.symm

end PottsContinuity.FKC.Medial
