module

public import PottsContinuity.Thm4.EdgeCutPathSystem
public import PottsContinuity.Thm4.ZeroReturnWinding

@[expose] public section

namespace PottsContinuity.Thm4
open PottsContinuity.PD.FK PottsContinuity.Thm4.Medial SimpleGraph
noncomputable section

local instance zeroPermutationPortFintype (n : ℕ) : Fintype (ParafermionicCoverFinitePort n) :=
  parafermionicCoverFinitePortFintype n

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

/-- The label-zero return of the actual terminal permutation is precisely the
geometric zero-return event in the queried-edge cut graph. -/
theorem terminalPermutation_zero_iff_edgeCutZeroReturn (n : ℕ) (hn : 1 ≤ n)
    (A : Configuration (ParafermionicAmbientGraph n))
    (e : (ParafermionicAmbientGraph n).edgeSet) :
    parafermionicCoverFiniteEdgeCutTerminalPermutation n hn A e 0 = 0 ↔
      EdgeCutZeroReturn n hn A e := by
  classical
  let s := parafermionicCoverFiniteEdgeCutSourceLabelsEquiv n hn e 0
  let t := parafermionicCoverFiniteEdgeCutSinkLabelsEquiv n hn e 0
  let partner := parafermionicCoverFiniteEdgeCutPartner n hn A e s.1
  have hpartner := parafermionicCoverFiniteEdgeCutPartner_spec n hn A e s.1
  have htarget := parafermionicCoverFiniteEdgeCutSourcePath_end_eq_sinkLabel n hn A e 0
  constructor
  · intro hzero
    have hreach := (parafermionicCoverFiniteEdgeCutSourcePath n hn A e 0).reachable
    rw [hzero, sinkLabel_zero_vertex] at htarget
    rw [sourceLabel_zero_vertex, htarget] at hreach
    exact hreach
  · intro hzero
    have hreach : (parafermionicCoverFiniteEdgeCutGraph n hn A e).Reachable s.1.1 t.1.1 := by
      simpa only [s, t, sourceLabel_zero_vertex, sinkLabel_zero_vertex, EdgeCutZeroReturn] using hzero
    have hdegree (v : ParafermionicCoverFiniteEdgeCutTerminal n hn e) :
        (parafermionicCoverFiniteEdgeCutGraph n hn A e).degree v.1 = 1 := by
      have hmem : v.val ∈ parafermionicCoverFiniteEdgeCutDegreeOneVertices n hn A e := by
        rw [← parafermionicCoverFiniteEdgeCutTerminals_eq_degreeOne n hn A e]
        exact v.2
      exact (Finset.mem_filter.mp hmem).2
    have htne : t.1.1 ≠ s.1.1 := by
      intro heq
      have hterminal : t.1 = s.1 := Subtype.ext heq
      exact t.2 (hterminal ▸ s.2)
    obtain ⟨r, _, huniq⟩ := parafermionicCoverFiniteEdgeCutGraph_existsUnique_partner
      n hn A e s.1.1 (hdegree s.1)
    have hpeq : partner.1 = t.1.1 :=
      (huniq partner.1 ⟨fun heq => hpartner.1 (Subtype.ext heq),
        hdegree partner, hpartner.2⟩).trans
          (huniq t.1.1 ⟨htne, hdegree t.1, hreach⟩).symm
    apply (parafermionicCoverFiniteEdgeCutSinkLabelsEquiv n hn e).injective
    apply Subtype.ext
    apply Subtype.ext
    exact htarget.symm.trans hpeq

/-- Zero-return probability-pair cancellation under the explicit self-dual law
for every real q ≥ 1; it therefore includes q=4 without a limiting argument. -/
theorem windingAtomicDefect_permutation_zero_probability_pair (n : ℕ) (hn : 1 ≤ n)
    (q : Set.Ici (1 : ℝ)) (ξ : BoundaryCondition (ParafermionicAmbientVertex n))
    (A : Configuration (ParafermionicAmbientGraph n))
    (e : (ParafermionicAmbientGraph n).edgeSet)
    (hzero : parafermionicCoverFiniteEdgeCutTerminalPermutation n hn A e 0 = 0) :
    configurationProbability (ParafermionicAmbientGraph n) (selfDualParameters q) ξ A *
        windingAtomicDefect n hn e A +
      configurationProbability (ParafermionicAmbientGraph n) (selfDualParameters q) ξ
        (toggleEdgeConfiguration e A) *
        windingAtomicDefect n hn e (toggleEdgeConfiguration e A) = 0 :=
  windingAtomicDefect_zero_return_probability_pair n hn (selfDualParameters q) ξ A e
    ((terminalPermutation_zero_iff_edgeCutZeroReturn n hn A e).1 hzero)

end
end PottsContinuity.Thm4
