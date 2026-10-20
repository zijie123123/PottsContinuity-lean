-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `Medial/ParafermionicCoverEdgeCutPathSystem.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.Medial.ParafermionicCoverEdgeCutTerminalPermutation
public import PottsContinuity.FKC.Medial.TwoTerminalGraph
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.FKC.FiniteFK

open PottsContinuity.FKC.Medial
open SimpleGraph
noncomputable section

local instance edgeCutPathPortFintype (n : ℕ) : Fintype (ParafermionicCoverFinitePort n) :=
  parafermionicCoverFinitePortFintype n

local instance edgeCutPathGraphDecidableRel (n : ℕ) (hn : 1 ≤ n)
    (A : Configuration (ParafermionicAmbientGraph n))
    (e : (ParafermionicAmbientGraph n).edgeSet) :
    DecidableRel (parafermionicCoverFiniteEdgeCutGraph n hn A e).Adj := Classical.decRel _

private theorem degree_one_vertex_mem_path_support_endpoints
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {s t : V}
    (p : G.Walk s t) (hp : p.IsPath) {v : V}
    (hdeg : G.degree v = 1) (hv : v ∈ p.support) : v = s ∨ v = t := by
  obtain ⟨i, hi, hil⟩ := Walk.mem_support_iff_exists_getVert.mp hv
  by_cases hi0 : i = 0
  · left
    subst i
    simpa using hi.symm
  by_cases hilend : i = p.length
  · right
    subst i
    simpa [Walk.getVert_length] using hi.symm
  · have hivs : p.getVert i ≠ s := by
      intro heq
      have hiEq := hp.getVert_injOn (by simpa using hil) (by simp)
        (heq.trans p.getVert_zero.symm)
      exact hi0 hiEq
    have hivt : p.getVert i ≠ t := by
      intro heq
      have hiEq := hp.getVert_injOn (by simpa using hil) (by simp)
        (heq.trans p.getVert_length.symm)
      exact hilend hiEq
    have hpathCard : (p.toSubgraph.neighborSet (p.getVert i)).ncard = 2 :=
      hp.ncard_neighborSet_toSubgraph_internal_eq_two hi0 (by omega)
    have hsub : p.toSubgraph.neighborSet (p.getVert i) ⊆ G.neighborSet (p.getVert i) := by
      intro z hz
      exact p.toSubgraph.adj_sub ((p.toSubgraph.mem_neighborSet _ _).mp hz)
    have hcard := Set.ncard_le_ncard hsub
    rw [hpathCard, G.ncard_neighborSet, hi, hdeg] at hcard
    omega

/-- Each labeled source terminal is joined to its actual partner by a chosen
simple path in the finite edge-cut graph. -/
def parafermionicCoverFiniteEdgeCutSourcePath (n : ℕ) (hn : 1 ≤ n)
    (A : Configuration (ParafermionicAmbientGraph n))
    (e : (ParafermionicAmbientGraph n).edgeSet) (i : Fin 3) :
    (parafermionicCoverFiniteEdgeCutGraph n hn A e).Walk
      (parafermionicCoverFiniteEdgeCutSourceLabelsEquiv n hn e i).1.1
      (parafermionicCoverFiniteEdgeCutPartner n hn A e
        (parafermionicCoverFiniteEdgeCutSourceLabelsEquiv n hn e i).1).1 := by
  classical
  exact Classical.choose
    ((parafermionicCoverFiniteEdgeCutTerminalPermutation_reachable n hn A e i).exists_isPath)

theorem parafermionicCoverFiniteEdgeCutSourcePath_isPath (n : ℕ) (hn : 1 ≤ n)
    (A : Configuration (ParafermionicAmbientGraph n))
    (e : (ParafermionicAmbientGraph n).edgeSet) (i : Fin 3) :
    (parafermionicCoverFiniteEdgeCutSourcePath n hn A e i).IsPath := by
  exact Classical.choose_spec
    ((parafermionicCoverFiniteEdgeCutTerminalPermutation_reachable n hn A e i).exists_isPath)

theorem parafermionicCoverFiniteEdgeCutSourcePath_unique (n : ℕ) (hn : 1 ≤ n)
    (A : Configuration (ParafermionicAmbientGraph n))
    (e : (ParafermionicAmbientGraph n).edgeSet) (i : Fin 3)
    (q : (parafermionicCoverFiniteEdgeCutGraph n hn A e).Walk
      (parafermionicCoverFiniteEdgeCutSourceLabelsEquiv n hn e i).1.1
      (parafermionicCoverFiniteEdgeCutPartner n hn A e
        (parafermionicCoverFiniteEdgeCutSourceLabelsEquiv n hn e i).1).1)
    (hq : q.IsPath) :
    q = parafermionicCoverFiniteEdgeCutSourcePath n hn A e i := by
  have hdeg := parafermionicCoverFiniteEdgeCutGraph_degree_le_two n hn A e
  have hs : (parafermionicCoverFiniteEdgeCutGraph n hn A e).degree
      (parafermionicCoverFiniteEdgeCutSourceLabelsEquiv n hn e i).1.1 = 1 := by
    have hmem : (parafermionicCoverFiniteEdgeCutSourceLabelsEquiv n hn e i).1.1 ∈
        parafermionicCoverFiniteEdgeCutDegreeOneVertices n hn A e := by
      rw [← parafermionicCoverFiniteEdgeCutTerminals_eq_degreeOne n hn A e]
      exact (parafermionicCoverFiniteEdgeCutSourceLabelsEquiv n hn e i).1.2
    exact (Finset.mem_filter.mp hmem).2
  exact (PottsContinuity.FKC.Medial.isPath_eq_of_degree_le_two
    (parafermionicCoverFiniteEdgeCutGraph n hn A e) hdeg hs q
    (parafermionicCoverFiniteEdgeCutSourcePath n hn A e i) hq
    (parafermionicCoverFiniteEdgeCutSourcePath_isPath n hn A e i))

/-- The chosen endpoint is exactly the sink label indexed by the actual
source-to-sink terminal permutation. -/
theorem parafermionicCoverFiniteEdgeCutSourcePath_end_eq_sinkLabel
    (n : ℕ) (hn : 1 ≤ n) (A : Configuration (ParafermionicAmbientGraph n))
    (e : (ParafermionicAmbientGraph n).edgeSet) (i : Fin 3) :
    (parafermionicCoverFiniteEdgeCutPartner n hn A e
      (parafermionicCoverFiniteEdgeCutSourceLabelsEquiv n hn e i).1).1 =
      (parafermionicCoverFiniteEdgeCutSinkLabelsEquiv n hn e
        (parafermionicCoverFiniteEdgeCutTerminalPermutation n hn A e i)).1.1 := by
  exact congrArg (fun t : ParafermionicCoverFiniteEdgeCutTerminal n hn e => t.1)
    (parafermionicCoverFiniteEdgeCutTerminalPermutation_sinkLabel n hn A e i).symm

/-- The unique simple source path meets no third degree-one terminal. -/
theorem parafermionicCoverFiniteEdgeCutSourcePath_terminals (n : ℕ) (hn : 1 ≤ n)
    (A : Configuration (ParafermionicAmbientGraph n))
    (e : (ParafermionicAmbientGraph n).edgeSet) (i : Fin 3)
    (r : ParafermionicCoverFiniteEdgeCutTerminal n hn e)
    (hr : r.1 ∈ (parafermionicCoverFiniteEdgeCutSourcePath n hn A e i).support) :
    r.1 = (parafermionicCoverFiniteEdgeCutSourceLabelsEquiv n hn e i).1.1 ∨
      r.1 = (parafermionicCoverFiniteEdgeCutPartner n hn A e
        (parafermionicCoverFiniteEdgeCutSourceLabelsEquiv n hn e i).1).1 := by
  have hdegree : (parafermionicCoverFiniteEdgeCutGraph n hn A e).degree r.1 = 1 := by
    have hmem : r.1 ∈ parafermionicCoverFiniteEdgeCutDegreeOneVertices n hn A e := by
      rw [← parafermionicCoverFiniteEdgeCutTerminals_eq_degreeOne n hn A e]
      exact r.2
    exact (Finset.mem_filter.mp hmem).2
  exact degree_one_vertex_mem_path_support_endpoints
    (parafermionicCoverFiniteEdgeCutGraph n hn A e)
    (parafermionicCoverFiniteEdgeCutSourcePath n hn A e i)
    (parafermionicCoverFiniteEdgeCutSourcePath_isPath n hn A e i)
    hdegree hr

/-- Paths from distinct source labels lie in different components of the actual
edge-cut graph, hence their vertex supports are disjoint. -/
theorem parafermionicCoverFiniteEdgeCutSourcePath_support_disjoint
    (n : ℕ) (hn : 1 ≤ n) (A : Configuration (ParafermionicAmbientGraph n))
    (e : (ParafermionicAmbientGraph n).edgeSet) {i j : Fin 3} (hij : i ≠ j) :
    List.Disjoint (parafermionicCoverFiniteEdgeCutSourcePath n hn A e i).support
      (parafermionicCoverFiniteEdgeCutSourcePath n hn A e j).support := by
  classical
  apply List.disjoint_left.mpr
  intro w hwi hwj
  let G := parafermionicCoverFiniteEdgeCutGraph n hn A e
  let si := parafermionicCoverFiniteEdgeCutSourceLabelsEquiv n hn e i
  let sj := parafermionicCoverFiniteEdgeCutSourceLabelsEquiv n hn e j
  let pi := parafermionicCoverFiniteEdgeCutPartner n hn A e si.1
  have hsiDegree : G.degree si.1.1 = 1 := by
    have hmem : si.1.1 ∈ parafermionicCoverFiniteEdgeCutDegreeOneVertices n hn A e := by
      rw [← parafermionicCoverFiniteEdgeCutTerminals_eq_degreeOne n hn A e]
      exact si.1.2
    exact (Finset.mem_filter.mp hmem).2
  obtain ⟨t, ht, huniq⟩ := parafermionicCoverFiniteEdgeCutGraph_existsUnique_partner
    n hn A e si.1.1 hsiDegree
  have hpi := parafermionicCoverFiniteEdgeCutPartner_spec n hn A e si.1
  have hpiDegree : G.degree pi.1 = 1 := by
    have hmem : pi.1 ∈ parafermionicCoverFiniteEdgeCutDegreeOneVertices n hn A e := by
      rw [← parafermionicCoverFiniteEdgeCutTerminals_eq_degreeOne n hn A e]
      exact pi.2
    exact (Finset.mem_filter.mp hmem).2
  have hpi_eq : pi.1 = t := huniq pi.1 ⟨by
    intro h
    exact hpi.1 (Subtype.ext h), hpiDegree, hpi.2⟩
  have hsource_ne : sj.1.1 ≠ si.1.1 := by
    intro h
    have hlabels : parafermionicCoverFiniteEdgeCutSourceLabelsEquiv n hn e j =
        parafermionicCoverFiniteEdgeCutSourceLabelsEquiv n hn e i := by
      apply Subtype.ext
      apply Subtype.ext
      exact h
    exact hij.symm ((parafermionicCoverFiniteEdgeCutSourceLabelsEquiv n hn e).injective hlabels)
  have hreach : G.Reachable si.1.1 sj.1.1 := by
    exact ((parafermionicCoverFiniteEdgeCutSourcePath n hn A e i).takeUntil w hwi).reachable.trans
      ((parafermionicCoverFiniteEdgeCutSourcePath n hn A e j).takeUntil w hwj).reachable.symm
  have hsource_eq_t : sj.1.1 = t := huniq sj.1.1 ⟨hsource_ne, by
    have hmem : sj.1.1 ∈ parafermionicCoverFiniteEdgeCutDegreeOneVertices n hn A e := by
      rw [← parafermionicCoverFiniteEdgeCutTerminals_eq_degreeOne n hn A e]
      exact sj.1.2
    exact (Finset.mem_filter.mp hmem).2, hreach⟩
  have hsource_eq_partner : sj.1.1 = pi.1 := hsource_eq_t.trans hpi_eq.symm
  have hterm_eq : sj.1 = pi := Subtype.ext hsource_eq_partner
  have hnotSource : ¬ parafermionicCoverFiniteEdgeCutSource n hn e pi := by
    intro hsourcePi
    exact (parafermionicCoverFiniteEdgeCutPartner_source_iff_not_source
      n hn A e si.1).mp hsourcePi si.2
  have hsourcePartner : parafermionicCoverFiniteEdgeCutSource n hn e pi := by
    rw [← hterm_eq]
    exact sj.2
  exact hnotSource hsourcePartner

end
end PottsContinuity.FKC.FiniteFK
