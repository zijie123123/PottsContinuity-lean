module

public import PottsContinuity.Thm4.FKCVisitBridge
public import PottsContinuity.Thm4.ThreeReturnConnection

@[expose] public section

namespace PottsContinuity.Thm4
open PottsContinuity.Thm4.Medial PottsContinuity.PD.FK
noncomputable section

/-- In the actual closed two-return class, the selected primal edge endpoints
are not connected by actual open edges. Transport uses exploration visits and
the selected unordered edge, without identifying the libraries' seed choices. -/
theorem closedTwoReturn_not_actualConnected (n : ℕ) (hn : 1 ≤ n)
    (A : Configuration (ParafermionicAmbientGraph n))
    (e : (ParafermionicAmbientGraph n).edgeSet) (he : e ∉ A)
    (h0 : parafermionicCoverFiniteEdgeCutTerminalPermutation n hn A e 0 ≠ 0)
    (h1 : parafermionicCoverFiniteEdgeCutTerminalPermutation n hn A e
      (parafermionicCoverFiniteEdgeCutTerminalPermutation n hn A e 0) = 0) :
    ¬ ActualConnected (ParafermionicAmbientGraph n) A
      (parafermionicCoverFinitePortPrimalVertex n
        (parafermionicCoverFiniteEdgeCutSeedPort n hn e))
      (parafermionicCoverFinitePortPrimalVertex n
        (parafermionicCoverFiniteEdgeCutSeedOrbit n hn e).openPort) := by
  have hclass := FKCBridge.fkc_closed_two_return n hn A e he h0 h1
  have hclosedF : fkcEdgeEquiv n e ∉ fkcConfiguration n A := by simpa using he
  have hsepF := PottsContinuity.FKC.FiniteFK.parafermionicCoverClosedTwoReturn_not_actualConnected
    n hn (fkcConfiguration n A) (fkcEdgeEquiv n e) hclosedF hclass.1 hclass.2
  let uF := PottsContinuity.FKC.FiniteFK.parafermionicCoverFinitePortPrimalVertex n
    (PottsContinuity.FKC.FiniteFK.parafermionicCoverFiniteEdgeCutSeedPort n hn (fkcEdgeEquiv n e))
  let vF := PottsContinuity.FKC.FiniteFK.parafermionicCoverFinitePortPrimalVertex n
    (PottsContinuity.FKC.FiniteFK.parafermionicCoverFiniteEdgeCutSeedOrbit n hn (fkcEdgeEquiv n e)).openPort
  have hsep : ¬ ActualConnected (ParafermionicAmbientGraph n) A uF vF := by
    intro hc
    exact hsepF ((fkc_actualConnected_iff n A uF vF).2 hc)
  let u := parafermionicCoverFinitePortPrimalVertex n
    (parafermionicCoverFiniteEdgeCutSeedPort n hn e)
  let v := parafermionicCoverFinitePortPrimalVertex n
    (parafermionicCoverFiniteEdgeCutSeedOrbit n hn e).openPort
  have hvalF := PottsContinuity.FKC.FiniteFK.parafermionicCoverFiniteEdgeCutSelectedEdge_eq_seedOpenPort_endpoints
    n hn (fkcEdgeEquiv n e)
  have hval := selectedEdge_eq_seedOpenPort_endpoints n hn e
  have hpairs : s(uF, vF) = s(u, v) := hvalF.symm.trans hval
  intro hconn
  change ActualConnected (ParafermionicAmbientGraph n) A u v at hconn
  rcases Sym2.eq_iff.mp hpairs with ⟨hu, hv⟩ | ⟨hu, hv⟩
  · apply hsep
    rw [hu, hv]
    exact hconn
  · apply hsep
    rw [hu, hv]
    exact hconn.symm

/-- Under free boundary, the actual closed two-return opening mass has reciprocal
self-dual factor sqrt(q), for every real q ≥ 1, including q=4. -/
theorem twoReturn_selfDual_free_probability (n : ℕ) (hn : 1 ≤ n)
    (q : Set.Ici (1 : ℝ)) (A : Configuration (ParafermionicAmbientGraph n))
    (e : (ParafermionicAmbientGraph n).edgeSet) (he : e ∉ A)
    (h0 : parafermionicCoverFiniteEdgeCutTerminalPermutation n hn A e 0 ≠ 0)
    (h1 : parafermionicCoverFiniteEdgeCutTerminalPermutation n hn A e
      (parafermionicCoverFiniteEdgeCutTerminalPermutation n hn A e 0) = 0) :
    configurationProbability (ParafermionicAmbientGraph n) (selfDualParameters q)
        (BoundaryCondition.free (∅ : Set (ParafermionicAmbientVertex n)))
        (toggleEdgeConfiguration e A) * loopWeight q =
      configurationProbability (ParafermionicAmbientGraph n) (selfDualParameters q)
        (BoundaryCondition.free (∅ : Set (ParafermionicAmbientVertex n))) A := by
  let G := ParafermionicAmbientGraph n
  let ξ := BoundaryCondition.free (∅ : Set (ParafermionicAmbientVertex n))
  let u := parafermionicCoverFinitePortPrimalVertex n
    (parafermionicCoverFiniteEdgeCutSeedPort n hn e)
  let v := parafermionicCoverFinitePortPrimalVertex n
    (parafermionicCoverFiniteEdgeCutSeedOrbit n hn e).openPort
  have hnonconn := closedTwoReturn_not_actualConnected n hn A e he h0 h1
  have heval := selectedEdge_eq_seedOpenPort_endpoints n hn e
  have huv : G.Adj u v := by
    apply G.mem_edgeSet.mp
    simpa [G, u, v, heval] using e.property
  have hsame : e = (⟨s(u, v), G.mem_edgeSet.mpr huv⟩ : G.edgeSet) := Subtype.ext heval
  have hnot : (⟨s(u, v), G.mem_edgeSet.mpr huv⟩ : G.edgeSet) ∉ A := by
    simpa only [← hsame] using he
  have hnotrel : ¬ (componentSetoid G ξ A).r u v := by
    change ¬ (componentSetoid G (BoundaryCondition.free ∅) A).r u v
    rw [componentSetoid_free]
    exact hnonconn
  have hprob := configurationProbability_insert_mul_loopWeight_of_not_related
    q ξ A huv hnot hnotrel
  simpa only [← hsame, toggleEdgeConfiguration, ite_eq_right he] using hprob

end
end PottsContinuity.Thm4
