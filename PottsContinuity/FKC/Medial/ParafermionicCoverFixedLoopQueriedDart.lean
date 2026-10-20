-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `Medial/ParafermionicCoverFixedLoopQueriedDart.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.Medial.ParafermionicCoverEdgeCutFixedLoop
public import Mathlib.Combinatorics.SimpleGraph.Walk.Operations
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.FKC.FiniteFK

open PottsContinuity.FKC.Medial
open SimpleGraph
noncomputable section

local instance queriedDartCornerGraphDecidableRel (n : ℕ) (hn : 1 ≤ n)
    (A : Configuration (ParafermionicAmbientGraph n)) :
    DecidableRel (parafermionicCoverFiniteCornerCutPairingGraph n hn A).Adj :=
  Classical.decRel _

local instance queriedDartCutGraphDecidableRel (n : ℕ) (hn : 1 ≤ n)
    (A : Configuration (ParafermionicAmbientGraph n))
    (e : (ParafermionicAmbientGraph n).edgeSet) :
    DecidableRel (parafermionicCoverFiniteEdgeCutGraph n hn A e).Adj :=
  Classical.decRel _

/-- The actual cut path contains no false-false dart querying the cut edge. -/
theorem parafermionicCoverFiniteEdgeCutSourcePath_cornerCut_false_false_not_queried
    (n : ℕ) (hn : 1 ≤ n) (A : Configuration (ParafermionicAmbientGraph n))
    (e : (ParafermionicAmbientGraph n).edgeSet) (i : ThreeTerminal)
    {d : (parafermionicCoverFiniteCornerCutPairingGraph n hn A).Dart}
    (hd : d ∈ (parafermionicCoverFiniteEdgeCutSourcePath_cornerCut n hn A e i).darts)
    (hfst : d.fst.2 = false) (hsnd : d.snd.2 = false) :
    parafermionicCoverPortEdge d.fst.1.1 ≠ parafermionicCoverFiniteEdgeEmbedding n e := by
  let p := parafermionicCoverFiniteEdgeCutSourcePath n hn A e i
  have hedge : d.edge ∈ p.edges := by
    have hcorner : d.edge ∈
        (parafermionicCoverFiniteEdgeCutSourcePath_cornerCut n hn A e i).edges := by
      rw [Walk.edges_eq_map_darts]
      exact List.mem_map.mpr ⟨d, hd, rfl⟩
    have heq :
        (parafermionicCoverFiniteEdgeCutSourcePath_cornerCut n hn A e i).edges = p.edges := by
      simp [p, parafermionicCoverFiniteEdgeCutSourcePath_cornerCut,
        Walk.edges_copy]
    simpa [heq] using hcorner
  have hadj := p.adj_of_mem_edges hedge
  have hfstEq : d.fst = (d.fst.1, false) := Prod.ext rfl hfst
  have hsndEq : d.snd = (d.snd.1, false) := Prod.ext rfl hsnd
  have hadj' : (parafermionicCoverFiniteEdgeCutGraph n hn A e).Adj
      (d.fst.1, false) (d.snd.1, false) := by
    rw [← hfstEq, ← hsndEq]
    exact hadj
  have hlocal :=
    (parafermionicCoverFiniteEdgeCutGraph_adj_false_false n hn A e
      d.fst.1 d.snd.1).mp hadj'
  rintro hquery
  have hsecond : parafermionicCoverPortEdge d.snd.1.1 =
      parafermionicCoverFiniteEdgeEmbedding n e := by
    calc
      parafermionicCoverPortEdge d.snd.1.1 =
          parafermionicCoverPortEdge
            (parafermionicCoverFiniteLocalPairPerm n A d.fst.1).1 := by
        exact congrArg (fun c : ParafermionicCoverFinitePort n =>
          parafermionicCoverPortEdge c.1) hlocal.1.symm
      _ = parafermionicCoverPortEdge d.fst.1.1 :=
        parafermionicCoverFiniteLocalPairPerm_edge_eq n A d.fst.1
      _ = parafermionicCoverFiniteEdgeEmbedding n e := hquery
  exact hlocal.2.2 ⟨hquery,hsecond⟩

/-- In the actual fixed loop, a false-false dart querying the selected edge is
exactly the restored sink-to-source concatenation dart. -/
theorem parafermionicCoverFiniteEdgeCutFixedLoop_queried_false_false_dart
    (n : ℕ) (hn : 1 ≤ n) (A : Configuration (ParafermionicAmbientGraph n))
    (e : (ParafermionicAmbientGraph n).edgeSet) (i : ThreeTerminal)
    (hi : i ≠ 0)
    (hfix : parafermionicCoverFiniteEdgeCutRoutingSuccessor n hn A e i = i)
    {d : (parafermionicCoverFiniteCornerCutPairingGraph n hn A).Dart}
    (hd : d ∈
      (parafermionicCoverFiniteEdgeCutFixedLoop n hn A e i hi hfix).darts)
    (hfst : d.fst.2 = false) (hsnd : d.snd.2 = false)
    (hquery : parafermionicCoverPortEdge d.fst.1.1 =
      parafermionicCoverFiniteEdgeEmbedding n e) :
    d.fst = (parafermionicCoverFiniteEdgeCutSinkLabels n hn e
        (parafermionicCoverFiniteEdgeCutTerminalPermutation n hn A e i)).1.1 ∧
      d.snd = (parafermionicCoverFiniteEdgeCutSourceLabels n hn e i).1.1 := by
  let p := parafermionicCoverFiniteEdgeCutSourcePath_cornerCut n hn A e i
  have hsucc : parafermionicCoverFiniteEdgeCutRoutingSuccessor n hn A e i ≠ 0 := by
    simpa [hfix] using hi
  have hadj : (parafermionicCoverFiniteCornerCutPairingGraph n hn A).Adj
      ((parafermionicCoverFiniteEdgeCutSinkLabels n hn e
        (parafermionicCoverFiniteEdgeCutTerminalPermutation n hn A e i)).1.1)
      ((parafermionicCoverFiniteEdgeCutSourceLabels n hn e i).1.1) := by
    simpa [hfix] using parafermionicCoverFiniteEdgeCutRoutingAdj n hn A e i hsucc
  have hnotpath : d ∉ p.darts := by
    intro hp
    exact (parafermionicCoverFiniteEdgeCutSourcePath_cornerCut_false_false_not_queried
      n hn A e i hp hfst hsnd) hquery
  have hd' : d ∈ (p.concat hadj).darts := by
    simpa [p, parafermionicCoverFiniteEdgeCutFixedLoop] using hd
  rw [Walk.darts_concat, List.concat_eq_append] at hd'
  simp only [List.mem_append, List.mem_singleton] at hd'
  rcases hd' with hp | hlast
  · exact (hnotpath hp).elim
  · subst d
    exact ⟨rfl,rfl⟩

end
end PottsContinuity.FKC.FiniteFK
