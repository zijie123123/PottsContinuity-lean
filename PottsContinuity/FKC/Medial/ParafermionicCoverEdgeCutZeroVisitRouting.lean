-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `Medial/ParafermionicCoverEdgeCutZeroVisitRouting.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.Medial.ParafermionicCoverEdgeVisitClassification
public import PottsContinuity.FKC.Medial.ParafermionicCoverEdgeCutPathSystem
public import PottsContinuity.FKC.Medial.ParafermionicCoverExplorationSupport
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.FKC.FiniteFK

open PottsContinuity.FKC.Medial
open SimpleGraph
noncomputable section

local instance zeroVisitPortFintype (n : ℕ) : Fintype (ParafermionicCoverFinitePort n) :=
  parafermionicCoverFinitePortFintype n

local instance zeroVisitCutGraphDecidableRel (n : ℕ) (hn : 1 ≤ n)
    (A : Configuration (ParafermionicAmbientGraph n))
    (e : (ParafermionicAmbientGraph n).edgeSet) :
    DecidableRel (parafermionicCoverFiniteEdgeCutGraph n hn A e).Adj := Classical.decRel _

private theorem sourceLabel_zero_vertex (n : ℕ) (hn : 1 ≤ n)
    (e : (ParafermionicAmbientGraph n).edgeSet) :
    (parafermionicCoverFiniteEdgeCutSourceLabelsEquiv n hn e 0).1.1 =
      (parafermionicCoverFiniteOriginCornerPort n hn, true) := by
  simp [parafermionicCoverFiniteEdgeCutSourceLabelsEquiv,
    parafermionicCoverFiniteEdgeCutSourceLabels, parafermionicCoverFiniteEdgeCutSourceCorner]

private theorem sinkLabel_zero_vertex (n : ℕ) (hn : 1 ≤ n)
    (e : (ParafermionicAmbientGraph n).edgeSet) :
    (parafermionicCoverFiniteEdgeCutSinkLabelsEquiv n hn e 0).1.1 =
      (parafermionicCoverFiniteCornerPairPerm n
        (parafermionicCoverFiniteOriginCornerPort n hn), true) := by
  simp [parafermionicCoverFiniteEdgeCutSinkLabelsEquiv,
    parafermionicCoverFiniteEdgeCutSinkLabels, parafermionicCoverFiniteEdgeCutSinkCorner]


private theorem edgeCutGraph_le_cornerCut (n : ℕ) (hn : 1 ≤ n)
    (A : Configuration (ParafermionicAmbientGraph n))
    (e : (ParafermionicAmbientGraph n).edgeSet) :
    parafermionicCoverFiniteEdgeCutGraph n hn A e ≤
      parafermionicCoverFiniteCornerCutPairingGraph n hn A := by
  intro u v huv
  exact huv.1

 def edgeCutWalkOfNoQueriedSupport (n : ℕ) (hn : 1 ≤ n)
    (A : Configuration (ParafermionicAmbientGraph n))
    (e : (ParafermionicAmbientGraph n).edgeSet) :
    ∀ {u v : ParafermionicCoverFinitePort n × Bool}
      (p : (parafermionicCoverFiniteCornerCutPairingGraph n hn A).Walk u v),
      (∀ c : ParafermionicCoverFinitePort n,
        parafermionicCoverPortEdge c.1 = parafermionicCoverFiniteEdgeEmbedding n e →
          (c, false) ∉ p.support) →
      (parafermionicCoverFiniteEdgeCutGraph n hn A e).Walk u v
  | _, _, .nil, _ => .nil
  | _, _, @SimpleGraph.Walk.cons _ _ u x v hadj tail, hno => by
      have hcut : (parafermionicCoverFiniteEdgeCutGraph n hn A e).Adj u x := by
        refine ⟨hadj, ?_⟩
        rintro ⟨hu, hx, hqu, hqx⟩
        have hxEq : x = (x.1, false) := by
          rcases x with ⟨port, flag⟩
          simp_all
        have hxSupport : x ∈ (SimpleGraph.Walk.cons hadj tail).support := by
          rw [SimpleGraph.Walk.support_cons]
          exact List.mem_cons_of_mem _ tail.start_mem_support
        exact hno x.1 hqx (hxEq ▸ hxSupport)
      have hnoTail : ∀ c : ParafermionicCoverFinitePort n,
          parafermionicCoverPortEdge c.1 = parafermionicCoverFiniteEdgeEmbedding n e →
            (c, false) ∉ tail.support := by
        intro c hc hmem
        apply hno c hc
        rw [SimpleGraph.Walk.support_cons]
        exact List.mem_cons_of_mem _ hmem
      exact SimpleGraph.Walk.cons hcut (edgeCutWalkOfNoQueriedSupport n hn A e tail hnoTail)

private theorem sourcePath_zero_no_query_false (n : ℕ) (hn : 1 ≤ n)
    (A : Configuration (ParafermionicAmbientGraph n))
    (e : (ParafermionicAmbientGraph n).edgeSet)
    (hperm : parafermionicCoverFiniteEdgeCutTerminalPermutation n hn A e 0 = 0)
    (c : ParafermionicCoverFinitePort n)
    (hquery : parafermionicCoverPortEdge c.1 = parafermionicCoverFiniteEdgeEmbedding n e) :
    (c, false) ∉ (parafermionicCoverFiniteEdgeCutSourcePath n hn A e 0).support := by
  intro hvisit
  have htarget := parafermionicCoverFiniteEdgeCutSourcePath_end_eq_sinkLabel n hn A e 0
  rw [hperm, sinkLabel_zero_vertex] at htarget
  have hterminal : (c, false) ∈ parafermionicCoverFiniteEdgeCutTerminals n hn e := by
    rw [parafermionicCoverFiniteEdgeCutTerminals]
    exact Finset.mem_union_left _
      ((parafermionicCoverFiniteEdgeCutQueriedFalse_mem_iff n e c).2 hquery)
  let r : ParafermionicCoverFiniteEdgeCutTerminal n hn e := ⟨(c, false), hterminal⟩
  have hends := parafermionicCoverFiniteEdgeCutSourcePath_terminals n hn A e 0 r hvisit
  rcases hends with hstart | hend
  · have hsource := sourceLabel_zero_vertex n hn e
    rw [hsource] at hstart
    exact Bool.noConfusion (congrArg Prod.snd hstart)
  · exact Bool.noConfusion (congrArg Prod.snd (hend.trans htarget))


theorem parafermionicCoverFiniteEdgeCutTerminalPermutation_zero_iff_edgeFalseVisits_zero
    (n : ℕ) (hn : 1 ≤ n) (A : Configuration (ParafermionicAmbientGraph n))
    (e : (ParafermionicAmbientGraph n).edgeSet) :
    parafermionicCoverFiniteEdgeCutTerminalPermutation n hn A e 0 = 0 ↔
      (parafermionicCoverFiniteEdgeFalseVisits n hn A e).card = 0 := by
  constructor
  · intro hperm
    apply (parafermionicCoverFiniteEdgeFalseVisits_card_eq_zero_iff n hn A e).2
    intro c hquery hvisit
    have hnoSource := sourcePath_zero_no_query_false n hn A e hperm c hquery
    have htarget := parafermionicCoverFiniteEdgeCutSourcePath_end_eq_sinkLabel n hn A e 0
    rw [hperm, sinkLabel_zero_vertex] at htarget
    let q : (parafermionicCoverFiniteCornerCutPairingGraph n hn A).Walk
        (parafermionicCoverFiniteOriginCornerPort n hn, true)
        (parafermionicCoverFiniteCornerPairPerm n
          (parafermionicCoverFiniteOriginCornerPort n hn), true) :=
      ((parafermionicCoverFiniteEdgeCutSourcePath n hn A e 0).mapLe
        (edgeCutGraph_le_cornerCut n hn A e)).copy
          (sourceLabel_zero_vertex n hn e) htarget
    have hqPath : q.IsPath := by
      simpa [q, SimpleGraph.Walk.support_copy,
        SimpleGraph.Walk.support_mapLe_eq_support] using
          parafermionicCoverFiniteEdgeCutSourcePath_isPath n hn A e 0
    have hqEq : q = parafermionicCoverFiniteOriginExplorationPath n hn A := by
      obtain ⟨p, hp, huniq⟩ := parafermionicCoverFiniteCornerCut_existsUnique_isPath n hn A
      exact (huniq q hqPath).trans
        (huniq (parafermionicCoverFiniteOriginExplorationPath n hn A)
          (parafermionicCoverFiniteOriginExplorationPath_isPath n hn A)).symm
    have hqVisit : (c, false) ∈ q.support := by
      rw [hqEq]
      exact hvisit
    exact hnoSource (by
      simpa [q, SimpleGraph.Walk.support_copy,
        SimpleGraph.Walk.support_mapLe_eq_support] using hqVisit)
  · intro hzero
    have hno := (parafermionicCoverFiniteEdgeFalseVisits_card_eq_zero_iff n hn A e).mp hzero
    let p := parafermionicCoverFiniteOriginExplorationPath n hn A
    let q := edgeCutWalkOfNoQueriedSupport n hn A e p hno
    let s := parafermionicCoverFiniteEdgeCutSourceLabelsEquiv n hn e 0
    let t := parafermionicCoverFiniteEdgeCutSinkLabelsEquiv n hn e 0
    have hreach : (parafermionicCoverFiniteEdgeCutGraph n hn A e).Reachable s.1.1 t.1.1 := by
      have h := q.reachable
      simpa [q, p, s, t, sourceLabel_zero_vertex, sinkLabel_zero_vertex] using h
    have hsDegree : (parafermionicCoverFiniteEdgeCutGraph n hn A e).degree s.1.1 = 1 := by
      have hmem : s.1.1 ∈ parafermionicCoverFiniteEdgeCutDegreeOneVertices n hn A e := by
        rw [← parafermionicCoverFiniteEdgeCutTerminals_eq_degreeOne n hn A e]
        exact s.1.2
      exact (Finset.mem_filter.mp hmem).2
    have htDegree : (parafermionicCoverFiniteEdgeCutGraph n hn A e).degree t.1.1 = 1 := by
      have hmem : t.1.1 ∈ parafermionicCoverFiniteEdgeCutDegreeOneVertices n hn A e := by
        rw [← parafermionicCoverFiniteEdgeCutTerminals_eq_degreeOne n hn A e]
        exact t.1.2
      exact (Finset.mem_filter.mp hmem).2
    have htNe : t.1.1 ≠ s.1.1 := by
      intro heq
      have hterminal : t.1 = s.1 := Subtype.ext heq
      exact t.2 (by rw [hterminal]; exact s.2)
    obtain ⟨r, _, huniq⟩ := parafermionicCoverFiniteEdgeCutGraph_existsUnique_partner
      n hn A e s.1.1 hsDegree
    let partner := parafermionicCoverFiniteEdgeCutPartner n hn A e s.1
    have hpartnerSpec := parafermionicCoverFiniteEdgeCutPartner_spec n hn A e s.1
    have hpartnerDegree : (parafermionicCoverFiniteEdgeCutGraph n hn A e).degree partner.1 = 1 := by
      have hmem : partner.1 ∈ parafermionicCoverFiniteEdgeCutDegreeOneVertices n hn A e := by
        rw [← parafermionicCoverFiniteEdgeCutTerminals_eq_degreeOne n hn A e]
        exact partner.2
      exact (Finset.mem_filter.mp hmem).2
    have hpartnerEq : partner.1 = t.1.1 := by
      have htarget := huniq t.1.1 ⟨htNe, htDegree, hreach⟩
      have hpartner := huniq partner.1 ⟨by
        intro heq
        exact hpartnerSpec.1 (Subtype.ext heq), hpartnerDegree, hpartnerSpec.2⟩
      exact hpartner.trans htarget.symm
    have hlabelEq : parafermionicCoverFiniteEdgeCutSinkLabelsEquiv n hn e
        (parafermionicCoverFiniteEdgeCutTerminalPermutation n hn A e 0) = t := by
      apply Subtype.ext
      apply Subtype.ext
      change (parafermionicCoverFiniteEdgeCutSinkLabels n hn e
          (parafermionicCoverFiniteEdgeCutTerminalPermutation n hn A e 0)).1.1 = t.1.1
      calc
        (parafermionicCoverFiniteEdgeCutSinkLabels n hn e
            (parafermionicCoverFiniteEdgeCutTerminalPermutation n hn A e 0)).1.1 = partner.1 := by
          exact congrArg (fun x : ParafermionicCoverFiniteEdgeCutTerminal n hn e => x.1)
            (parafermionicCoverFiniteEdgeCutTerminalPermutation_sinkLabel n hn A e 0)
        _ = t.1.1 := hpartnerEq
    have hindex := (parafermionicCoverFiniteEdgeCutSinkLabelsEquiv n hn e).injective hlabelEq
    exact hindex


end
end PottsContinuity.FKC.FiniteFK

