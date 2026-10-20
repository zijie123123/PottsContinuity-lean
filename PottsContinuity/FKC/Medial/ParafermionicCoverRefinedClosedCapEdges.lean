-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `Medial/ParafermionicCoverRefinedClosedCapEdges.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.Medial.ParafermionicCoverRefinedPairingRoutes
public import PottsContinuity.FKC.Medial.ParafermionicCoverRefinedPairingSimplicity
public import PottsContinuity.FKC.Medial.ParafermionicCoverRefinedPairingRouteInteriorShape
public import PottsContinuity.FKC.Medial.GraphWalkPathSubstitution
public import Mathlib.Combinatorics.SimpleGraph.Walk.Operations
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.FKC.Medial

open SimpleGraph PottsContinuity.FKC.FiniteFK
noncomputable section

/-- Every edge of the literal refined closed cap route for an actual false-false
corner-cut dart occurs in the substituted walk. -/
theorem parafermionicCoverRefinedClosedCapWalk_edges_subset_pairingWalk
    (n : ℕ) (hn : 1 ≤ n) (A : Configuration (ParafermionicAmbientGraph n))
    {u v : ParafermionicCoverFinitePort n × Bool}
    (p : (parafermionicCoverFiniteCornerCutPairingGraph n hn A).Walk u v)
    (d : (parafermionicCoverFiniteCornerCutPairingGraph n hn A).Dart)
    (hd : d ∈ p.darts) (hfst : d.fst.2 = false) (hsnd : d.snd.2 = false)
    (hstate : parafermionicCoverPortBondState
      (parafermionicCoverConfigurationExtensionState n A) d.fst.1.1 = false) :
    (parafermionicCoverRefinedClosedCapWalk d.fst.1.1).edges ⊆
      (parafermionicCoverRefinedPairingWalk n hn A p).edges := by
  have hfst' : d.fst = (d.fst.1, false) := Prod.ext rfl hfst
  have hsnd' : d.snd = (d.snd.1, false) := Prod.ext rfl hsnd
  have hadj : (parafermionicCoverFiniteCornerCutPairingGraph n hn A).Adj
      (d.fst.1, false) (d.snd.1, false) := by
    rw [← hfst', ← hsnd']
    exact d.adj
  have hend := parafermionicCoverRefinedPairingRoute_false_false_endpoint
    n hn A d.fst.1 d.snd.1 hadj
  have hpair : d.snd.1 = parafermionicCoverClosedPair d.fst.1.1 := by
    rcases hend with hopen | hclosed
    · have : false = true := hstate.symm.trans hopen.1
      exact False.elim (Bool.noConfusion this)
    · exact hclosed.2
  let q := parafermionicCoverRefinedPairingRoute n hn A d.adj
  have hqSupport : q.support =
      (parafermionicCoverRefinedClosedCapWalk d.fst.1.1).support := by
    rw [parafermionicCoverRefinedPairingRoute_support,
      parafermionicCoverRefinedClosedCapWalk_support]
    simp [parafermionicCoverRefinedPairingRouteSupport, hfst, hsnd,
      hstate, hpair, parafermionicCoverRefinedPairingEmbedding]
  have hqEdges : q.edges =
      (parafermionicCoverRefinedClosedCapWalk d.fst.1.1).edges := by
    rw [Walk.edges_eq_zipWith_support, Walk.edges_eq_zipWith_support, hqSupport]
  intro e he
  have hroute : e ∈ q.edges := by rw [hqEdges]; exact he
  rw [Walk.edges_eq_map_darts] at hroute ⊢
  change e ∈ (graphWalkSubstitute
    (parafermionicCoverFiniteCornerCutPairingGraph n hn A)
    parafermionicCoverGraph parafermionicCoverRefinedPairingEmbedding
    (fun {a b} h => parafermionicCoverRefinedPairingRoute n hn A h) p).darts.map Dart.edge
  rw [graphWalkSubstitute_darts_flatMap]
  rcases List.mem_map.mp hroute with ⟨rd, hrd, hedge⟩
  apply List.mem_map.mpr
  refine ⟨rd, List.mem_flatMap.mpr ⟨d, hd, hrd⟩, hedge⟩

end
end PottsContinuity.FKC.Medial
