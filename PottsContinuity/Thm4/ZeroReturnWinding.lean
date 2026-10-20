module

public import PottsContinuity.Thm4.EdgeCutGraph
public import PottsContinuity.Thm4.PathTerminals
public import PottsContinuity.Thm4.EndpointDefect

/-!
# Winding cancellation for the actual zero-return event

The event is literal reachability of the original two corner terminals after
cutting the queried edge's false-layer pairings. We prove that it is equivalent
to absence of queried false-layer visits and is invariant under the edge toggle.
The walk restriction helpers are ported from
FKconvergence/Medial/ParafermionicCoverEdgeCutZeroVisitRouting.lean;
the vertical-support argument reuses the proof in Thm4/ZeroTurn.lean.
No terminal-permutation or nonzero-return cancellation is assumed.
-/

@[expose] public section

namespace PottsContinuity.Thm4
open PottsContinuity.PD.FK PottsContinuity.Thm4.Medial SimpleGraph
noncomputable section

local instance zeroReturnPortFintype (n : ℕ) : Fintype (ParafermionicCoverFinitePort n) :=
  parafermionicCoverFinitePortFintype n

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

private theorem finiteCornerCut_support_adj
    (n : ℕ) (hn : 1 ≤ n) (A : Configuration (ParafermionicAmbientGraph n))
    {u v : ParafermionicCoverFinitePort n × Bool}
    (hu : u ∈ (parafermionicCoverFiniteOriginExplorationPath n hn A).support)
    (hadj : (parafermionicCoverFiniteCornerCutPairingGraph n hn A).Adj u v) :
    v ∈ (parafermionicCoverFiniteOriginExplorationPath n hn A).support := by
  let L := parafermionicCoverFiniteLocalPairPerm n A
  let C := parafermionicCoverFiniteCornerPairPerm n
  let s := parafermionicCoverFiniteOriginCornerPort n hn
  let B := pairingSingleCutPerm C s (parafermionicCoverFiniteCornerPairPerm_involutive n)
  have hL := parafermionicCoverFiniteLocalPairPerm_involutive n A
  have hC := parafermionicCoverFiniteCornerPairPerm_involutive n
  have hB := pairingSingleCut_involutive C s hC
  have hfree := parafermionicCoverFiniteLocalPairPerm_no_fixed_points n A
  have hst : s ≠ C s := parafermionicCoverFiniteCornerPairPerm_origin_ne n hn
  have hBfixed : ∀ x, B x = x ↔ x = s ∨ x = C s := by
    intro x
    exact pairingSingleCutPerm_fixed_iff C s x hC
      (parafermionicCoverFiniteCornerPairPerm_no_fixed_points n)
  have hgraph : parafermionicCoverFiniteCornerCutPairingGraph n hn A =
      pairingGraph L B hL hB := rfl
  rw [hgraph] at hadj
  exact pairingGraph_path_support_closed_under_adj L B hL hB hfree hst hBfixed
    (parafermionicCoverFiniteOriginExplorationPath n hn A)
    (parafermionicCoverFiniteOriginExplorationPath_isPath n hn A) hu hadj

private theorem finiteCornerCut_vertical_support_iff
    (n : ℕ) (hn : 1 ≤ n) (A : Configuration (ParafermionicAmbientGraph n))
    (c : ParafermionicCoverFinitePort n) :
    ((c, false) ∈ (parafermionicCoverFiniteOriginExplorationPath n hn A).support) ↔
      ((c, true) ∈ (parafermionicCoverFiniteOriginExplorationPath n hn A).support) := by
  constructor
  · intro h
    apply finiteCornerCut_support_adj n hn A h
    simp [parafermionicCoverFiniteCornerCutPairingGraph, pairingGraph]
  · intro h
    apply finiteCornerCut_support_adj n hn A h
    simp [parafermionicCoverFiniteCornerCutPairingGraph, pairingGraph]

/-- The source and target remain connected after cutting the queried edge. -/
def EdgeCutZeroReturn (n : ℕ) (hn : 1 ≤ n)
    (A : Configuration (ParafermionicAmbientGraph n))
    (e : (ParafermionicAmbientGraph n).edgeSet) : Prop :=
  (parafermionicCoverFiniteEdgeCutGraph n hn A e).Reachable
    (parafermionicCoverFiniteOriginCornerPort n hn, true)
    (parafermionicCoverFiniteCornerPairPerm n
      (parafermionicCoverFiniteOriginCornerPort n hn), true)

/-- Zero return is exactly absence of a visit to the queried false-layer ports. -/
theorem edgeCutZeroReturn_iff_no_false_visits (n : ℕ) (hn : 1 ≤ n)
    (A : Configuration (ParafermionicAmbientGraph n))
    (e : (ParafermionicAmbientGraph n).edgeSet) :
    EdgeCutZeroReturn n hn A e ↔
      ∀ c : ParafermionicCoverFinitePort n,
        parafermionicCoverPortEdge c.1 = parafermionicCoverFiniteEdgeEmbedding n e →
          (c, false) ∉ (parafermionicCoverFiniteOriginExplorationPath n hn A).support := by
  classical
  constructor
  · intro hzero c hquery hvisit
    obtain ⟨p, hp⟩ := hzero.exists_isPath
    let q := p.mapLe (edgeCutGraph_le_cornerCut n hn A e)
    have hq : q.IsPath := by
      simpa only [q, Walk.isPath_def, Walk.support_mapLe_eq_support] using hp
    have hqeq : q = parafermionicCoverFiniteOriginExplorationPath n hn A := by
      obtain ⟨r, hr, huniq⟩ := parafermionicCoverFiniteCornerCut_existsUnique_isPath n hn A
      exact (huniq q hq).trans
        (huniq _ (parafermionicCoverFiniteOriginExplorationPath_isPath n hn A)).symm
    have hmem : (c, false) ∈ p.support := by
      have : (c, false) ∈ q.support := hqeq.symm ▸ hvisit
      simpa only [q, Walk.support_mapLe_eq_support] using this
    have hdeg : (parafermionicCoverFiniteEdgeCutGraph n hn A e).degree (c, false) = 1 := by
      rw [parafermionicCoverFiniteEdgeCutGraph_degree_false, ite_eq_left hquery]
    rcases degree_one_vertex_mem_path_support_endpoints
      (parafermionicCoverFiniteEdgeCutGraph n hn A e) p hp hdeg hmem with h | h
    all_goals exact Bool.noConfusion (congrArg Prod.snd h)
  · intro hno
    exact (edgeCutWalkOfNoQueriedSupport n hn A e
      (parafermionicCoverFiniteOriginExplorationPath n hn A) hno).reachable

/-- The zero-return class is unchanged when the actual queried edge is toggled. -/
theorem edgeCutZeroReturn_toggle_iff (n : ℕ) (hn : 1 ≤ n)
    (A : Configuration (ParafermionicAmbientGraph n))
    (e : (ParafermionicAmbientGraph n).edgeSet) :
    EdgeCutZeroReturn n hn (toggleEdgeConfiguration e A) e ↔ EdgeCutZeroReturn n hn A e := by
  unfold EdgeCutZeroReturn
  rw [← parafermionicCoverFiniteEdgeCutGraph_toggle_eq n hn A e]

private theorem windingEdgePorts_query (n : ℕ)
    (e : (ParafermionicAmbientGraph n).edgeSet) (c : ParafermionicCoverFinitePort n)
    (hc : c ∈ windingEdgePorts n e) :
    parafermionicCoverPortEdge c.1 = parafermionicCoverFiniteEdgeEmbedding n e := by
  classical
  apply Subtype.ext
  have hval := (Finset.mem_filter.mp hc).2.2
  exact hval.trans (embeddedEdgeEmbedding_coe
    (ParafermionicAmbientGraph n) parafermionicCoverGraph
    (parafermionicCoverBoxVertexEmbedding n) (parafermionicCoverBoxGraph_map_le n) e).symm

/-- On the actual zero-return event, both winding defects vanish individually. -/
theorem windingAtomicDefect_zero_return_pair (n : ℕ) (hn : 1 ≤ n)
    (A : Configuration (ParafermionicAmbientGraph n))
    (e : (ParafermionicAmbientGraph n).edgeSet)
    (hzero : EdgeCutZeroReturn n hn A e) :
    windingAtomicDefect n hn e A = 0 ∧
      windingAtomicDefect n hn e (toggleEdgeConfiguration e A) = 0 := by
  have hT := (edgeCutZeroReturn_toggle_iff n hn A e).2 hzero
  constructor
  · apply windingAtomicDefect_eq_zero_of_no_visits
    intro c hc hvisit
    apply (edgeCutZeroReturn_iff_no_false_visits n hn A e).1 hzero c
      (windingEdgePorts_query n e c hc)
    exact (finiteCornerCut_vertical_support_iff n hn A c).2 hvisit
  · apply windingAtomicDefect_eq_zero_of_no_visits
    intro c hc hvisit
    apply (edgeCutZeroReturn_iff_no_false_visits n hn (toggleEdgeConfiguration e A) e).1 hT c
      (windingEdgePorts_query n e c hc)
    exact (finiteCornerCut_vertical_support_iff n hn (toggleEdgeConfiguration e A) c).2 hvisit

/-- Zero-return winding cancellation holds under every actual finite FK law. -/
theorem windingAtomicDefect_zero_return_probability_pair (n : ℕ) (hn : 1 ≤ n)
    (P : Parameters) (ξ : BoundaryCondition (ParafermionicAmbientVertex n))
    (A : Configuration (ParafermionicAmbientGraph n))
    (e : (ParafermionicAmbientGraph n).edgeSet)
    (hzero : EdgeCutZeroReturn n hn A e) :
    configurationProbability (ParafermionicAmbientGraph n) P ξ A *
        windingAtomicDefect n hn e A +
      configurationProbability (ParafermionicAmbientGraph n) P ξ (toggleEdgeConfiguration e A) *
        windingAtomicDefect n hn e (toggleEdgeConfiguration e A) = 0 := by
  obtain ⟨hA, hT⟩ := windingAtomicDefect_zero_return_pair n hn A e hzero
  simp only [hA, hT, mul_zero, add_zero]

end
end PottsContinuity.Thm4
