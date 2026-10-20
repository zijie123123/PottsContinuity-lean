-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `Medial/ParafermionicCoverEdgeCutTurnInvariant.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.Medial.ParafermionicCoverEdgeCutReconnectionTurn
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.FKC.FiniteFK

open PottsContinuity.FKC.Medial
open SimpleGraph
noncomputable section

local instance edgeCutTurnInvariantPortFintype (n : ℕ) :
    Fintype (ParafermionicCoverFinitePort n) := parafermionicCoverFinitePortFintype n

local instance edgeCutTurnInvariantGraphDecidableRel (n : ℕ) (hn : 1 ≤ n)
    (A : Configuration (ParafermionicAmbientGraph n))
    (e : (ParafermionicAmbientGraph n).edgeSet) :
    DecidableRel (parafermionicCoverFiniteEdgeCutGraph n hn A e).Adj := Classical.decRel _

private theorem edgeCutTurnInvariant_mapDart_endpoints
    {V : Type*} {G G' : SimpleGraph V} (h : G ≤ G') (d : G.Dart) :
    ((SimpleGraph.Hom.ofLE h).mapDart d).fst = d.fst ∧
      ((SimpleGraph.Hom.ofLE h).mapDart d).snd = d.snd := by
  simp [SimpleGraph.Hom.mapDart_apply, SimpleGraph.Hom.ofLE]

private theorem parafermionicCoverMedialTurnPositive_toggle_eq_of_bond_state_eq
    (ω τ : ParafermionicCoverConfiguration) (c : ParafermionicCoverPort)
    (h : parafermionicCoverPortBondState ω c = parafermionicCoverPortBondState τ c) :
    parafermionicCoverMedialTurnPositive ω c = parafermionicCoverMedialTurnPositive τ c := by
  have hbase : parafermionicCoverPortLocalBaseState ω c c.1.bond =
      parafermionicCoverPortLocalBaseState τ c c.1.bond := by
    rw [parafermionicCoverPortLocalBaseState_at,
      parafermionicCoverPortLocalBaseState_at, h]
  unfold parafermionicCoverMedialTurnPositive medialTurnPositive
  rw [hbase]

private theorem parafermionicCoverMedialTurnExponent_toggle_eq_of_edge_ne
    (n : ℕ) (A : Configuration (ParafermionicAmbientGraph n))
    (e : (ParafermionicAmbientGraph n).edgeSet) (c : ParafermionicCoverPort)
    (hne : parafermionicCoverPortEdge c ≠ parafermionicCoverFiniteEdgeEmbedding n e) :
    parafermionicCoverMedialTurnExponent
        (parafermionicCoverConfigurationExtensionState n (toggleEdgeConfiguration e A)) c =
      parafermionicCoverMedialTurnExponent
        (parafermionicCoverConfigurationExtensionState n A) c := by
  have hstate := parafermionicCoverPortBondState_toggle n A e c
  have hstate' : parafermionicCoverPortBondState
      (parafermionicCoverConfigurationExtensionState n (toggleEdgeConfiguration e A)) c =
        parafermionicCoverPortBondState
          (parafermionicCoverConfigurationExtensionState n A) c := by
    rw [hstate, ite_eq_right hne]
  have hpositive := parafermionicCoverMedialTurnPositive_toggle_eq_of_bond_state_eq
    _ _ c hstate'
  simp [parafermionicCoverMedialTurnExponent, hpositive]

theorem parafermionicCoverFiniteEdgeCutStepTurn_toggle_eq_of_adj
    (n : ℕ) (hn : 1 ≤ n) (A : Configuration (ParafermionicAmbientGraph n))
    (e : (ParafermionicAmbientGraph n).edgeSet)
    {u v : ParafermionicCoverFinitePort n × Bool}
    (h : (parafermionicCoverFiniteEdgeCutGraph n hn A e).Adj u v) :
    parafermionicCoverFinitePairingStepTurn n A u v =
      parafermionicCoverFinitePairingStepTurn n (toggleEdgeConfiguration e A) u v := by
  rcases u with ⟨c, b⟩
  rcases v with ⟨d, b'⟩
  cases b <;> cases b'
  · have hcut := (parafermionicCoverFiniteEdgeCutGraph_adj_false_false n hn A e c d).mp h
    have hne : parafermionicCoverPortEdge c.1 ≠
        parafermionicCoverFiniteEdgeEmbedding n e := by
      intro hc
      have hd : parafermionicCoverPortEdge d.1 =
          parafermionicCoverFiniteEdgeEmbedding n e := by
        calc
          parafermionicCoverPortEdge d.1 =
              parafermionicCoverPortEdge
                (parafermionicCoverFiniteLocalPairPerm n A c).1 := by
                  rw [hcut.1]
          _ = parafermionicCoverPortEdge c.1 :=
                parafermionicCoverFiniteLocalPairPerm_edge_eq n A c
          _ = parafermionicCoverFiniteEdgeEmbedding n e := hc
      exact hcut.2.2 ⟨hc, hd⟩
    have hturn := parafermionicCoverMedialTurnExponent_toggle_eq_of_edge_ne n A e c.1 hne
    simpa [parafermionicCoverFinitePairingStepTurn] using hturn.symm
  · simp [parafermionicCoverFinitePairingStepTurn]
  · simp [parafermionicCoverFinitePairingStepTurn]
  · simp [parafermionicCoverFinitePairingStepTurn]

theorem parafermionicCoverFiniteEdgeCutWalkTurn_toggle_eq
    (n : ℕ) (hn : 1 ≤ n) (A : Configuration (ParafermionicAmbientGraph n))
    (e : (ParafermionicAmbientGraph n).edgeSet)
    {u v : ParafermionicCoverFinitePort n × Bool}
    (p : (parafermionicCoverFiniteEdgeCutGraph n hn A e).Walk u v) :
    parafermionicCoverFinitePairingWalkTurn n hn A
        (p.mapLe (show parafermionicCoverFiniteEdgeCutGraph n hn A e ≤
          parafermionicCoverFiniteCornerCutPairingGraph n hn A from fun _ _ h => h.1)) =
      parafermionicCoverFinitePairingWalkTurn n hn
        (toggleEdgeConfiguration e A)
        (p.mapLe (show parafermionicCoverFiniteEdgeCutGraph n hn A e ≤
          parafermionicCoverFiniteCornerCutPairingGraph n hn
            (toggleEdgeConfiguration e A) from by
              intro x y hxy
              have htoggle := parafermionicCoverFiniteEdgeCutGraph_toggle_eq n hn A e
              rw [htoggle] at hxy
              exact hxy.1)) := by
  let hleA : parafermionicCoverFiniteEdgeCutGraph n hn A e ≤
      parafermionicCoverFiniteCornerCutPairingGraph n hn A := fun _ _ h => h.1
  let hleT : parafermionicCoverFiniteEdgeCutGraph n hn A e ≤
      parafermionicCoverFiniteCornerCutPairingGraph n hn (toggleEdgeConfiguration e A) := by
    intro x y hxy
    have htoggle := parafermionicCoverFiniteEdgeCutGraph_toggle_eq n hn A e
    rw [htoggle] at hxy
    exact hxy.1
  have hturns :
      (p.darts.map (fun d => parafermionicCoverFinitePairingStepTurn n A d.fst d.snd)).sum =
        (p.darts.map (fun d => parafermionicCoverFinitePairingStepTurn n
          (toggleEdgeConfiguration e A) d.fst d.snd)).sum := by
    apply congrArg List.sum
    apply List.map_congr_left
    intro d hd
    exact parafermionicCoverFiniteEdgeCutStepTurn_toggle_eq_of_adj n hn A e d.adj
  have hturnA : parafermionicCoverFinitePairingWalkTurn n hn A (p.mapLe hleA) =
      (p.darts.map (fun d => parafermionicCoverFinitePairingStepTurn n A
        d.fst d.snd)).sum := by
    unfold parafermionicCoverFinitePairingWalkTurn
    rw [SimpleGraph.Walk.mapLe, SimpleGraph.Walk.darts_map, List.map_map]
    apply congrArg List.sum
    apply List.map_congr_left
    intro d hd
    obtain ⟨hfst, hsnd⟩ := edgeCutTurnInvariant_mapDart_endpoints hleA d
    simp
  have hturnT : parafermionicCoverFinitePairingWalkTurn n hn
      (toggleEdgeConfiguration e A) (p.mapLe hleT) =
      (p.darts.map (fun d => parafermionicCoverFinitePairingStepTurn n
        (toggleEdgeConfiguration e A) d.fst d.snd)).sum := by
    unfold parafermionicCoverFinitePairingWalkTurn
    rw [SimpleGraph.Walk.mapLe, SimpleGraph.Walk.darts_map, List.map_map]
    apply congrArg List.sum
    apply List.map_congr_left
    intro d hd
    obtain ⟨hfst, hsnd⟩ := edgeCutTurnInvariant_mapDart_endpoints hleT d
    simp
  rw [hturnA, hturnT]
  exact hturns

end
end PottsContinuity.FKC.FiniteFK
