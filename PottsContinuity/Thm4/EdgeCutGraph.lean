/- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
accessible (see `related_formalizations` in formalization.yaml): file
`Medial/ParafermionicCoverEdgeCutGraph.lean`.
Adaptation: namespace relocation; reuse existing orientation adjacency API.
-/
module

public import PottsContinuity.Thm4.ExplorationOrientation
public import PottsContinuity.Thm4.FiniteEdgePort
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.Thm4

open PottsContinuity.PD.FK PottsContinuity.Thm4.Medial
open SimpleGraph
noncomputable section

local instance edgeCutPortFintype (n : ℕ) : Fintype (ParafermionicCoverFinitePort n) :=
  parafermionicCoverFinitePortFintype n

/-- The actual finite-edge cut graph on the existing two-layer medial carrier.
It removes precisely the false-layer local-pair edges whose two port occurrences
query the selected actual lifted primal edge. -/
def parafermionicCoverFiniteEdgeCutGraph (n : ℕ) (hn : 1 ≤ n)
    (A : Configuration (ParafermionicAmbientGraph n))
    (e : (ParafermionicAmbientGraph n).edgeSet) :
    SimpleGraph (ParafermionicCoverFinitePort n × Bool) where
  Adj u v :=
    (parafermionicCoverFiniteCornerCutPairingGraph n hn A).Adj u v ∧
      ¬ (u.2 = false ∧ v.2 = false ∧
        parafermionicCoverPortEdge u.1.1 = parafermionicCoverFiniteEdgeEmbedding n e ∧
        parafermionicCoverPortEdge v.1.1 = parafermionicCoverFiniteEdgeEmbedding n e)
  symm := by
    constructor
    intro u v ⟨hadj, hnot⟩
    refine ⟨hadj.symm, ?_⟩
    intro h
    rcases h with ⟨hu, hv, hqv, hqu⟩
    exact hnot ⟨hv, hu, hqu, hqv⟩
  loopless := by
    constructor
    intro u ⟨hadj, _⟩
    exact hadj.ne rfl

local instance edgeCutGraphDecidableRel (n : ℕ) (hn : 1 ≤ n)
    (A : Configuration (ParafermionicAmbientGraph n))
    (e : (ParafermionicAmbientGraph n).edgeSet) :
    DecidableRel (parafermionicCoverFiniteEdgeCutGraph n hn A e).Adj := Classical.decRel _

local instance cornerCutGraphDecidableRel (n : ℕ) (hn : 1 ≤ n)
    (A : Configuration (ParafermionicAmbientGraph n)) :
    DecidableRel (parafermionicCoverFiniteCornerCutPairingGraph n hn A).Adj := by
  simpa [parafermionicCoverFiniteCornerCutPairingGraph] using
    pairingGraph_decidableAdj
      (parafermionicCoverFiniteLocalPairPerm n A)
      (pairingSingleCutPerm (parafermionicCoverFiniteCornerPairPerm n)
        (parafermionicCoverFiniteOriginCornerPort n hn)
        (parafermionicCoverFiniteCornerPairPerm_involutive n))
      (parafermionicCoverFiniteLocalPairPerm_involutive n A)
      (pairingSingleCut_involutive (parafermionicCoverFiniteCornerPairPerm n)
        (parafermionicCoverFiniteOriginCornerPort n hn)
        (parafermionicCoverFiniteCornerPairPerm_involutive n))

@[simp] theorem parafermionicCoverFiniteEdgeCutGraph_adj_iff
    (n : ℕ) (hn : 1 ≤ n) (A : Configuration (ParafermionicAmbientGraph n))
    (e : (ParafermionicAmbientGraph n).edgeSet)
    (u v : ParafermionicCoverFinitePort n × Bool) :
    (parafermionicCoverFiniteEdgeCutGraph n hn A e).Adj u v ↔
      (parafermionicCoverFiniteCornerCutPairingGraph n hn A).Adj u v ∧
        ¬ (u.2 = false ∧ v.2 = false ∧
          parafermionicCoverPortEdge u.1.1 = parafermionicCoverFiniteEdgeEmbedding n e ∧
          parafermionicCoverPortEdge v.1.1 = parafermionicCoverFiniteEdgeEmbedding n e) := Iff.rfl

theorem parafermionicCoverFiniteEdgeCutGraph_adj_false_false
    (n : ℕ) (hn : 1 ≤ n) (A : Configuration (ParafermionicAmbientGraph n))
    (e : (ParafermionicAmbientGraph n).edgeSet)
    (c d : ParafermionicCoverFinitePort n) :
    (parafermionicCoverFiniteEdgeCutGraph n hn A e).Adj (c, false) (d, false) ↔
      parafermionicCoverFiniteLocalPairPerm n A c = d ∧ c ≠ d ∧
        ¬ (parafermionicCoverPortEdge c.1 = parafermionicCoverFiniteEdgeEmbedding n e ∧
          parafermionicCoverPortEdge d.1 = parafermionicCoverFiniteEdgeEmbedding n e) := by
  rw [parafermionicCoverFiniteEdgeCutGraph_adj_iff,
    parafermionicCoverFiniteCornerCutPairingGraph_adj_iff]
  simp [and_assoc]

theorem parafermionicCoverFiniteEdgeCutGraph_adj_false_true
    (n : ℕ) (hn : 1 ≤ n) (A : Configuration (ParafermionicAmbientGraph n))
    (e : (ParafermionicAmbientGraph n).edgeSet)
    (c d : ParafermionicCoverFinitePort n) :
    (parafermionicCoverFiniteEdgeCutGraph n hn A e).Adj (c, false) (d, true) ↔ c = d := by
  rw [parafermionicCoverFiniteEdgeCutGraph_adj_iff,
    parafermionicCoverFiniteCornerCutPairingGraph_adj_iff]
  simp

theorem parafermionicCoverFiniteEdgeCutGraph_adj_true_false
    (n : ℕ) (hn : 1 ≤ n) (A : Configuration (ParafermionicAmbientGraph n))
    (e : (ParafermionicAmbientGraph n).edgeSet)
    (c d : ParafermionicCoverFinitePort n) :
    (parafermionicCoverFiniteEdgeCutGraph n hn A e).Adj (c, true) (d, false) ↔ c = d := by
  rw [parafermionicCoverFiniteEdgeCutGraph_adj_iff,
    parafermionicCoverFiniteCornerCutPairingGraph_adj_iff]
  simp

theorem parafermionicCoverFiniteEdgeCutGraph_adj_true_true
    (n : ℕ) (hn : 1 ≤ n) (A : Configuration (ParafermionicAmbientGraph n))
    (e : (ParafermionicAmbientGraph n).edgeSet)
    (c d : ParafermionicCoverFinitePort n) :
    (parafermionicCoverFiniteEdgeCutGraph n hn A e).Adj (c, true) (d, true) ↔
      pairingSingleCutPerm (parafermionicCoverFiniteCornerPairPerm n)
        (parafermionicCoverFiniteOriginCornerPort n hn)
        (parafermionicCoverFiniteCornerPairPerm_involutive n) c = d ∧ c ≠ d := by
  rw [parafermionicCoverFiniteEdgeCutGraph_adj_iff,
    parafermionicCoverFiniteCornerCutPairingGraph_adj_iff]
  simp

/-- The local pairing preserves the queried actual primal edge. -/
theorem parafermionicCoverFiniteLocalPairPerm_edge_eq (n : ℕ)
    (A : Configuration (ParafermionicAmbientGraph n)) (c : ParafermionicCoverFinitePort n) :
    parafermionicCoverPortEdge
        (parafermionicCoverFiniteLocalPairPerm n A c).1 =
      parafermionicCoverPortEdge c.1 := by
  apply Subtype.ext
  exact parafermionicCoverLocalPair_edge_val_eq
    (parafermionicCoverConfigurationExtensionState n A) c.1

theorem parafermionicCoverFiniteEdgeCutGraph_neighborFinset_false
    (n : ℕ) (hn : 1 ≤ n) (A : Configuration (ParafermionicAmbientGraph n))
    (e : (ParafermionicAmbientGraph n).edgeSet) (c : ParafermionicCoverFinitePort n) :
    (parafermionicCoverFiniteEdgeCutGraph n hn A e).neighborFinset (c, false) =
      if parafermionicCoverPortEdge c.1 = parafermionicCoverFiniteEdgeEmbedding n e then
        {(c, true)}
      else
        {(c, true), (parafermionicCoverFiniteLocalPairPerm n A c, false)} := by
  classical
  have hlocal : parafermionicCoverPortEdge
      (parafermionicCoverFiniteLocalPairPerm n A c).1 =
      parafermionicCoverPortEdge c.1 := parafermionicCoverFiniteLocalPairPerm_edge_eq n A c
  ext x
  rcases x with ⟨d, b⟩
  cases b
  · rw [mem_neighborFinset, parafermionicCoverFiniteEdgeCutGraph_adj_false_false]
    by_cases hq : parafermionicCoverPortEdge c.1 = parafermionicCoverFiniteEdgeEmbedding n e
    · have hbad : ¬ (parafermionicCoverFiniteLocalPairPerm n A c = d ∧ c ≠ d ∧
          ¬ (parafermionicCoverPortEdge c.1 = parafermionicCoverFiniteEdgeEmbedding n e ∧
            parafermionicCoverPortEdge d.1 = parafermionicCoverFiniteEdgeEmbedding n e)) := by
        rintro ⟨hp, _, hnot⟩
        apply hnot
        refine ⟨hq, ?_⟩
        calc
          parafermionicCoverPortEdge d.1 =
              parafermionicCoverPortEdge (parafermionicCoverFiniteLocalPairPerm n A c).1 :=
                congrArg (fun z : ParafermionicCoverFinitePort n => parafermionicCoverPortEdge z.1) hp.symm
          _ = parafermionicCoverPortEdge c.1 := hlocal
          _ = parafermionicCoverFiniteEdgeEmbedding n e := hq
      simp only [ite_eq_left hq, Finset.mem_singleton, Prod.mk.injEq, Bool.false_eq_true,
        and_false]
      constructor
      · exact hbad
      · intro h
        cases h
    · simp only [ite_eq_right hq, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq,
        Bool.false_eq_true, and_false, false_or]
      constructor
      · rintro ⟨hp, hne, _⟩
        exact ⟨hp.symm, trivial⟩
      · rintro ⟨hd, _⟩
        refine ⟨hd.symm, ?_, ?_⟩
        · intro hcd
          exact parafermionicCoverFiniteLocalPairPerm_no_fixed_points n A c
            (hd.symm.trans hcd.symm)
        · intro hboth
          apply hq
          calc
            parafermionicCoverPortEdge c.1 =
                parafermionicCoverPortEdge (parafermionicCoverFiniteLocalPairPerm n A c).1 := hlocal.symm
            _ = parafermionicCoverPortEdge d.1 :=
              congrArg (fun z : ParafermionicCoverFinitePort n => parafermionicCoverPortEdge z.1) hd.symm
            _ = parafermionicCoverFiniteEdgeEmbedding n e := hboth.2
  · rw [mem_neighborFinset, parafermionicCoverFiniteEdgeCutGraph_adj_false_true]
    by_cases hq : parafermionicCoverPortEdge c.1 = parafermionicCoverFiniteEdgeEmbedding n e <;>
      simp [hq, eq_comm]

theorem parafermionicCoverFiniteEdgeCutGraph_degree_false
    (n : ℕ) (hn : 1 ≤ n) (A : Configuration (ParafermionicAmbientGraph n))
    (e : (ParafermionicAmbientGraph n).edgeSet) (c : ParafermionicCoverFinitePort n) :
    (parafermionicCoverFiniteEdgeCutGraph n hn A e).degree (c, false) =
      if parafermionicCoverPortEdge c.1 = parafermionicCoverFiniteEdgeEmbedding n e then 1 else 2 := by
  classical
  rw [SimpleGraph.degree, parafermionicCoverFiniteEdgeCutGraph_neighborFinset_false]
  split_ifs <;> simp

theorem parafermionicCoverFiniteEdgeCutGraph_degree_true_of_fixed
    (n : ℕ) (hn : 1 ≤ n) (A : Configuration (ParafermionicAmbientGraph n))
    (e : (ParafermionicAmbientGraph n).edgeSet) (c : ParafermionicCoverFinitePort n)
    (hfix : pairingSingleCutPerm (parafermionicCoverFiniteCornerPairPerm n)
      (parafermionicCoverFiniteOriginCornerPort n hn)
      (parafermionicCoverFiniteCornerPairPerm_involutive n) c = c) :
    (parafermionicCoverFiniteEdgeCutGraph n hn A e).degree (c, true) = 1 := by
  have hset : (parafermionicCoverFiniteEdgeCutGraph n hn A e).neighborSet (c, true) =
      (parafermionicCoverFiniteCornerCutPairingGraph n hn A).neighborSet (c, true) := by
    ext d
    change (parafermionicCoverFiniteEdgeCutGraph n hn A e).Adj (c, true) d ↔
      (parafermionicCoverFiniteCornerCutPairingGraph n hn A).Adj (c, true) d
    rcases d with ⟨d, b⟩
    cases b
    · rw [parafermionicCoverFiniteEdgeCutGraph_adj_true_false]
      rw [parafermionicCoverFiniteCornerCutPairingGraph_adj_iff]
      simp
    · rw [parafermionicCoverFiniteEdgeCutGraph_adj_true_true]
      rw [parafermionicCoverFiniteCornerCutPairingGraph_adj_iff]
      simp
  rw [← SimpleGraph.ncard_neighborSet, hset]
  have hbase := pairingGraph_degree_true_of_fixed
      (parafermionicCoverFiniteLocalPairPerm n A)
      (pairingSingleCutPerm (parafermionicCoverFiniteCornerPairPerm n)
        (parafermionicCoverFiniteOriginCornerPort n hn)
        (parafermionicCoverFiniteCornerPairPerm_involutive n))
      (parafermionicCoverFiniteLocalPairPerm_involutive n A)
      (pairingSingleCut_involutive (parafermionicCoverFiniteCornerPairPerm n)
        (parafermionicCoverFiniteOriginCornerPort n hn)
        (parafermionicCoverFiniteCornerPairPerm_involutive n)) hfix
  rw [← SimpleGraph.ncard_neighborSet] at hbase
  simpa [parafermionicCoverFiniteCornerCutPairingGraph] using hbase

theorem parafermionicCoverFiniteEdgeCutGraph_degree_true_of_not_fixed
    (n : ℕ) (hn : 1 ≤ n) (A : Configuration (ParafermionicAmbientGraph n))
    (e : (ParafermionicAmbientGraph n).edgeSet) (c : ParafermionicCoverFinitePort n)
    (hfix : pairingSingleCutPerm (parafermionicCoverFiniteCornerPairPerm n)
      (parafermionicCoverFiniteOriginCornerPort n hn)
      (parafermionicCoverFiniteCornerPairPerm_involutive n) c ≠ c) :
    (parafermionicCoverFiniteEdgeCutGraph n hn A e).degree (c, true) = 2 := by
  have hset : (parafermionicCoverFiniteEdgeCutGraph n hn A e).neighborSet (c, true) =
      (parafermionicCoverFiniteCornerCutPairingGraph n hn A).neighborSet (c, true) := by
    ext d
    change (parafermionicCoverFiniteEdgeCutGraph n hn A e).Adj (c, true) d ↔
      (parafermionicCoverFiniteCornerCutPairingGraph n hn A).Adj (c, true) d
    rcases d with ⟨d, b⟩
    cases b
    · rw [parafermionicCoverFiniteEdgeCutGraph_adj_true_false]
      rw [parafermionicCoverFiniteCornerCutPairingGraph_adj_iff]
      simp
    · rw [parafermionicCoverFiniteEdgeCutGraph_adj_true_true]
      rw [parafermionicCoverFiniteCornerCutPairingGraph_adj_iff]
      simp
  rw [← SimpleGraph.ncard_neighborSet, hset]
  have hbase := pairingGraph_degree_true_of_ne
      (parafermionicCoverFiniteLocalPairPerm n A)
      (pairingSingleCutPerm (parafermionicCoverFiniteCornerPairPerm n)
        (parafermionicCoverFiniteOriginCornerPort n hn)
        (parafermionicCoverFiniteCornerPairPerm_involutive n))
      (parafermionicCoverFiniteLocalPairPerm_involutive n A)
      (pairingSingleCut_involutive (parafermionicCoverFiniteCornerPairPerm n)
        (parafermionicCoverFiniteOriginCornerPort n hn)
        (parafermionicCoverFiniteCornerPairPerm_involutive n)) hfix
  rw [← SimpleGraph.ncard_neighborSet] at hbase
  simpa [parafermionicCoverFiniteCornerCutPairingGraph] using hbase

/-- Deleting the queried false-layer edge makes the cut graph independent of the
state of that actual primal edge. -/
theorem parafermionicCoverFiniteEdgeCutGraph_toggle_eq
    (n : ℕ) (hn : 1 ≤ n) (A : Configuration (ParafermionicAmbientGraph n))
    (e : (ParafermionicAmbientGraph n).edgeSet) :
    parafermionicCoverFiniteEdgeCutGraph n hn A e =
      parafermionicCoverFiniteEdgeCutGraph n hn (toggleEdgeConfiguration e A) e := by
  classical
  ext u v
  rcases u with ⟨c, b⟩
  rcases v with ⟨d, b'⟩
  cases b <;> cases b'
  · rw [parafermionicCoverFiniteEdgeCutGraph_adj_iff,
      parafermionicCoverFiniteEdgeCutGraph_adj_iff]
    let E := parafermionicCoverFiniteEdgeEmbedding n e
    have hbaseA :
        (parafermionicCoverFiniteCornerCutPairingGraph n hn A).Adj (c, false) (d, false) ↔
          parafermionicCoverFiniteLocalPairPerm n A c = d ∧ c ≠ d := by
      rw [parafermionicCoverFiniteCornerCutPairingGraph_adj_iff]
      simp
    have hbaseT :
        (parafermionicCoverFiniteCornerCutPairingGraph n hn (toggleEdgeConfiguration e A)).Adj
            (c, false) (d, false) ↔
          parafermionicCoverFiniteLocalPairPerm n (toggleEdgeConfiguration e A) c = d ∧ c ≠ d := by
      rw [parafermionicCoverFiniteCornerCutPairingGraph_adj_iff]
      simp
    rw [hbaseA, hbaseT]
    simp only [
      true_and]
    by_cases hc : parafermionicCoverPortEdge c.1 = E
    · have hiff : ∀ B : Configuration (ParafermionicAmbientGraph n),
          parafermionicCoverFiniteLocalPairPerm n B c = d →
          parafermionicCoverPortEdge d.1 = E := by
        intro B hpair
        calc
          parafermionicCoverPortEdge d.1 =
              parafermionicCoverPortEdge (parafermionicCoverFiniteLocalPairPerm n B c).1 :=
                congrArg (fun z : ParafermionicCoverFinitePort n => parafermionicCoverPortEdge z.1)
                  hpair.symm
          _ = parafermionicCoverPortEdge c.1 := parafermionicCoverFiniteLocalPairPerm_edge_eq n B c
          _ = E := hc
      constructor
      · intro h
        rcases h with ⟨⟨hpair, hne⟩, hnot⟩
        have hnot' : ¬ (parafermionicCoverPortEdge c.1 = E ∧
            parafermionicCoverPortEdge d.1 = E) := by simpa using hnot
        exact False.elim (hnot' ⟨hc, hiff A hpair⟩)
      · intro h
        rcases h with ⟨⟨hpair, hne⟩, hnot⟩
        have hnot' : ¬ (parafermionicCoverPortEdge c.1 = E ∧
            parafermionicCoverPortEdge d.1 = E) := by simpa using hnot
        exact False.elim (hnot' ⟨hc, hiff (toggleEdgeConfiguration e A) hpair⟩)
    · have hlocal := parafermionicCoverLocalPair_toggle_eq_of_edge_ne n A e c.1 hc
      have hperm : parafermionicCoverFiniteLocalPairPerm n
          (toggleEdgeConfiguration e A) c = parafermionicCoverFiniteLocalPairPerm n A c := by
        apply Subtype.ext
        simpa only [parafermionicCoverFiniteLocalPairPerm_val] using hlocal
      simp [hperm]
  · rw [parafermionicCoverFiniteEdgeCutGraph_adj_iff,
      parafermionicCoverFiniteEdgeCutGraph_adj_iff,
      parafermionicCoverFiniteCornerCutPairingGraph_adj_iff,
      parafermionicCoverFiniteCornerCutPairingGraph_adj_iff]
    simp
  · rw [parafermionicCoverFiniteEdgeCutGraph_adj_iff,
      parafermionicCoverFiniteEdgeCutGraph_adj_iff,
      parafermionicCoverFiniteCornerCutPairingGraph_adj_iff,
      parafermionicCoverFiniteCornerCutPairingGraph_adj_iff]
    simp
  · rw [parafermionicCoverFiniteEdgeCutGraph_adj_iff,
      parafermionicCoverFiniteEdgeCutGraph_adj_iff,
      parafermionicCoverFiniteCornerCutPairingGraph_adj_iff,
      parafermionicCoverFiniteCornerCutPairingGraph_adj_iff]
    simp

end
end PottsContinuity.Thm4
