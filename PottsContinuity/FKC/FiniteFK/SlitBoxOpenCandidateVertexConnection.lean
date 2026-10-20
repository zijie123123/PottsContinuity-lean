-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/SlitBoxOpenCandidateVertexConnection.lean`, with
-- module and namespace relocated (wrappers of the SLE development replaced by `PottsContinuity.FKC.SLEWrap`)
-- and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.SlitBoxCandidateEdgeSupport
public import PottsContinuity.FKC.FiniteFK.ActualConnectionFirstHitPath
public import PottsContinuity.FKC.FiniteFK.SlitBoxBottomCenter
public import Mathlib.Combinatorics.SimpleGraph.Walk.Decomp
public import Mathlib.Combinatorics.SimpleGraph.Walk.Maps
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.FKC.FiniteFK

open PottsContinuity.FKC

/-- An ordered walk all of whose actual edges are open transfers to the
actual open graph, and hence witnesses actual connectivity. -/
theorem actualConnected_of_walk_edges_open
    {V : Type*} {G : SimpleGraph V} (A : Configuration G)
    {x y : V} (w : G.Walk x y)
    (hopen : ∀ e, e ∈ w.edges → e ∈ openEdges G A) :
    ActualConnected G A x y := by
  apply (actualConnected_iff_walk G A x y).2
  refine ⟨w.transfer (openGraph G A) ?_⟩
  intro e he
  rw [openGraph_edgeSet]
  exact hopen e he

/-- Every vertex on an ordered path whose traversed edges belong to `A` is
actually connected to the path endpoint by open edges. The path itself is
transferred to `openGraph`; support inclusion alone is not used as a proxy for
connectivity. -/
theorem actualConnected_of_mem_support_of_walk_edges_open
    {V : Type*} [DecidableEq V] {G : SimpleGraph V} (A : Configuration G)
    {x y v : V} (w : G.Walk x y)
    (hopen : ∀ e, e ∈ w.edges → e ∈ openEdges G A)
    (hv : v ∈ w.support) :
    ActualConnected G A v y := by
  have hxy : ActualConnected G A x y := actualConnected_of_walk_edges_open A w hopen
  let pre := w.takeUntil v hv
  have hxv : ActualConnected G A x v :=
    actualConnected_of_walk_edges_open A pre (by
      intro e he
      exact hopen e (w.edges_takeUntil_subset_edges hv he))
  exact hxv.symm.trans hxy

/-- A fixed first-hit candidate whose original path is contained in the
configuration connects every vertex on that actual path to its wired-arc
endpoint. -/
theorem slitBoxCandidate_vertex_actualConnected_to_endpoint_of_open
    (n : ℕ) (u : SlitBoxVertex n) (p : SlitBoxFirstHitBaseCandidates n u)
    (A : Configuration (slitBoxGraph n))
    (hopen : slitBoxCandidateOriginalPathEdgeSupport n u p ⊆ A)
    (v : SlitBoxVertex n)
    (hv : v ∈ (p.val.2 : (slitBoxGraph n).Walk u p.val.1).support) :
    ActualConnected (slitBoxGraph n) A v p.val.1 := by
  let w : (slitBoxGraph n).Walk u p.val.1 := p.val.2
  apply actualConnected_of_mem_support_of_walk_edges_open A
    w
  · intro e he
    have heGraph : e ∈ (slitBoxGraph n).edgeSet := w.edges_subset_edgeSet he
    let eGraph : (slitBoxGraph n).edgeSet := ⟨e, heGraph⟩
    have hsupport : eGraph ∈ slitBoxCandidateOriginalPathEdgeSupport n u p :=
      (mem_slitBoxCandidateOriginalPathEdgeSupport_iff n u p eGraph).2 (by
        simpa [eGraph] using he)
    have hA : eGraph ∈ A := hopen hsupport
    exact ⟨eGraph, hA, rfl⟩
  · exact hv

/-- If the literal bottom-center vertex lies on an open candidate's original
path, that same candidate certifies an actual wired-arc hit from the center.
This is the positive branch complementary to the separate off-path argument. -/
theorem slitBoxBottomCenter_actual_arc_hit_of_candidate_path_open
    (n : ℕ) (u : SlitBoxVertex n)
    (p : SlitBoxFirstHitBaseCandidates n u)
    (A : Configuration (slitBoxGraph n))
    (hopen : slitBoxCandidateOriginalPathEdgeSupport n u p ⊆ A)
    (hcenter : (slitBoxBottomCenterVertex n : SlitBoxVertex n) ∈
      (p.val.2 : (slitBoxGraph n).Walk u p.val.1).support) :
    A ∈ slitBoxWiredArcConnectionEvent n (slitBoxBottomCenterVertex n) := by
  have hconn := slitBoxCandidate_vertex_actualConnected_to_endpoint_of_open
    n u p A hopen (slitBoxBottomCenterVertex n) hcenter
  exact ⟨p.val.1, p.property.1, hconn⟩

end PottsContinuity.FKC.FiniteFK
