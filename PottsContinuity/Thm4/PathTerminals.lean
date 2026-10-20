/- Degree-one path lemma adapted from FKconvergence, an earlier formalization by the same author
that is not publicly accessible (see `related_formalizations` in formalization.yaml): file
`Medial/ParafermionicCoverEdgeCutPathSystem.lean`.
Adaptation: standalone generic lemma; no terminal-label dependencies.
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.Thm4.Medial
open SimpleGraph

theorem degree_one_vertex_mem_path_support_endpoints
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

end PottsContinuity.Thm4.Medial
