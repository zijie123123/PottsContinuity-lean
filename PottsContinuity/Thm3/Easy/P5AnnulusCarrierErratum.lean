module

public import PottsContinuity.DualityExt.PositiveAnnulusDualShell
public import PottsContinuity.DualityExt.PositiveDualSubgraphLaw
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Maps

@[expose] public section

namespace PottsContinuity.Thm3.Easy

open PottsContinuity.PD.FK
open PottsContinuity.DualityExt

def annulusDualExpandedHostAnchor (N : ℕ) : LatticeVertex :=
  ((annulusHostAnchor N).1 - 1, (annulusHostAnchor N).2 - 1)

noncomputable def annulusExpandedHostCarrierEquiv (N : ℕ) :
    RectangleVertex (annulusDualExpandedHostAnchor N) (4 * N + 1) (4 * N + 1) ≃
      RectangleDualVertex (annulusHostAnchor N) (4 * N) (4 * N) := by
  refine {
    toFun := fun v => ⟨v.1, ?_⟩
    invFun := fun v => ⟨v.1, ?_⟩
    left_inv := ?_
    right_inv := ?_ }
  · simpa [rectangleDualExpanded, annulusDualExpandedHostAnchor] using v.2
  · simpa [rectangleDualExpanded, annulusDualExpandedHostAnchor] using v.2
  · intro v
    apply Subtype.ext
    rfl
  · intro v
    apply Subtype.ext
    rfl

noncomputable def annulusExpandedHostDualCandidateGraph (N : ℕ) :
    SimpleGraph (RectangleVertex (annulusDualExpandedHostAnchor N)
      (4 * N + 1) (4 * N + 1)) :=
  (rectangleSubgraphDualGraph (annulusSourceGraph_map_le_host N)).comap
    (annulusExpandedHostCarrierEquiv N)

theorem annulusExpandedHostDualCandidateGraph_le_rectangle (N : ℕ) :
    annulusExpandedHostDualCandidateGraph N ≤
      rectangleGraph (annulusDualExpandedHostAnchor N) (4 * N + 1) (4 * N + 1) := by
  intro u v huv
  have hdual : (rectangleSubgraphDualGraph
      (annulusSourceGraph_map_le_host N)).Adj
      (annulusExpandedHostCarrierEquiv N u)
      (annulusExpandedHostCarrierEquiv N v) := huv
  have hhost : (rectangleDualGraph (annulusHostAnchor N) (4 * N) (4 * N)).Adj
      (annulusExpandedHostCarrierEquiv N u)
      (annulusExpandedHostCarrierEquiv N v) :=
    (edgeRestriction_le (rectangleDualGraph (annulusHostAnchor N) (4 * N) (4 * N))
      (rectangleSubgraphRemovedDualEdges (annulusSourceGraph_map_le_host N))) hdual
  have hamb := rectangleDualGraph_le_ambient (annulusHostAnchor N) (4 * N) (4 * N) hhost
  have hcoords : squareLattice.Adj u.1 v.1 := by
    have h := (rectangleDualAmbientGraph_adj_iff
      (annulusHostAnchor N) (4 * N) (4 * N)
      (annulusExpandedHostCarrierEquiv N u)
      (annulusExpandedHostCarrierEquiv N v)).mp hamb
    simpa [annulusExpandedHostCarrierEquiv] using h
  exact (rectangleGraph_adj_iff (annulusDualExpandedHostAnchor N)
    (4 * N + 1) (4 * N + 1) u v).2 hcoords

theorem annulusExpandedHostDualCandidateGraph_map_eq (N : ℕ) :
    (annulusExpandedHostDualCandidateGraph N).map
      (annulusExpandedHostCarrierEquiv N).toEmbedding =
      rectangleSubgraphDualGraph (annulusSourceGraph_map_le_host N) := by
  apply SimpleGraph.ext
  funext u v
  apply propext
  rw [SimpleGraph.map_adj]
  constructor
  · rintro ⟨x, y, hxy, rfl, rfl⟩
    exact hxy
  · intro huv
    refine ⟨(annulusExpandedHostCarrierEquiv N).symm u,
      (annulusExpandedHostCarrierEquiv N).symm v, ?_, by simp, by simp⟩
    exact huv

end PottsContinuity.Thm3.Easy
