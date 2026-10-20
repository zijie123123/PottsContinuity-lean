/- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
accessible (see `related_formalizations` in formalization.yaml): file
`FiniteFK/RectangleDoubleCollarDualRemaining.lean`.
Adaptation: namespace/import relocation; reuse existing PD/BD12 carriers.
Independent interior edge probability and every real q>=1 (PD.FK.Parameters).
No upper bound q<4 is used in this finite proof. -/
module

public import PottsContinuity.PlanarMixed.Square.RectangleDoubleCollarDualEdges
public import PottsContinuity.PD.Duality.RectangleDualConfiguration
public import PottsContinuity.PD.FK.EdgeRestriction
public import PottsContinuity.PlanarMixed.Square.Extras
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.DeleteEdges

@[expose] public section

namespace PottsContinuity.PlanarMixed.Square
open PD.FK PD.FK.Medial PD.Duality BD12
open scoped PottsContinuity.PlanarMixed.Square

open PD.FK PD.FK.Medial

noncomputable section

local instance rectangleDoubleCollarDualRemainingOuterEdgeDecidableEq
    (a : LatticeVertex) (w h : ℕ) :
    DecidableEq (rectangleDoubleCollarDualOuterGraph a w h).edgeSet := Classical.decEq _

/-- Actual outer primal edge labels belonging to the embedded inner rectangle. -/
def rectangleDoubleCollarInnerPrimalEdges (a : LatticeVertex) (w h : ℕ) :
    Finset (rectanglePrimalEdgeCarrier (a.1, a.2 - 1) w (h + 2)) := by
  classical
  exact Finset.univ.map (rectangleDoubleCollarPrimalEdgeEmbedding a w h)

@[simp] theorem mem_rectangleDoubleCollarInnerPrimalEdges
    (a : LatticeVertex) (w h : ℕ)
    (e : rectanglePrimalEdgeCarrier (a.1, a.2 - 1) w (h + 2)) :
    e ∈ rectangleDoubleCollarInnerPrimalEdges a w h ↔
      ∃ f : rectanglePrimalEdgeCarrier a w h,
        rectangleDoubleCollarPrimalEdgeEmbedding a w h f = e := by
  simp [rectangleDoubleCollarInnerPrimalEdges]

theorem rectangleDoubleCollarInnerPrimalEdges_mem_iff_embedding
    (a : LatticeVertex) (w h : ℕ)
    (e : rectanglePrimalEdgeCarrier (a.1, a.2 - 1) w (h + 2)) :
    e ∈ rectangleDoubleCollarInnerPrimalEdges a w h ↔
      ∃ f : rectanglePrimalEdgeCarrier a w h,
        rectangleDoubleCollarPrimalEdgeEmbedding a w h f = e := by
  classical
  rw [mem_rectangleDoubleCollarInnerPrimalEdges]

theorem rectanglePrimalDualEdgeEquiv_apply_primalEdge_double
    {a : LatticeVertex} {w h : ℕ}
    (e : RectangleDualEdgeCarrier a w h) :
    rectanglePrimalDualEdgeEquiv a w h e.primalEdge = e := by
  cases e with
  | mk p cb hcb => subst cb; rfl

theorem rectangleDoubleCollarDualEdgeEmbedding_mem
    (a : LatticeVertex) (w h : ℕ) (e : RectangleDualEdgeCarrier a w h) :
    (rectangleDoubleCollarDualEdgeEmbedding a w h e).primalEdge ∈
      rectangleDoubleCollarInnerPrimalEdges a w h := by
  rw [rectangleDoubleCollarDualEdgeEmbedding_primalEdge]
  exact (rectangleDoubleCollarInnerPrimalEdges_mem_iff_embedding a w h _).mpr
    ⟨e.primalEdge, rfl⟩

theorem rectangleDoubleCollarDualEdgeEmbedding_mem_iff
    (a : LatticeVertex) (w h : ℕ)
    (e : RectangleDualEdgeCarrier (a.1, a.2 - 1) w (h + 2)) :
    e.primalEdge ∈ rectangleDoubleCollarInnerPrimalEdges a w h ↔
      ∃ f : RectangleDualEdgeCarrier a w h,
        rectangleDoubleCollarDualEdgeEmbedding a w h f = e := by
  constructor
  · intro he
    rcases (rectangleDoubleCollarInnerPrimalEdges_mem_iff_embedding a w h
      e.primalEdge).mp he with ⟨f, hf⟩
    let dI := rectanglePrimalDualEdgeEquiv a w h f
    refine ⟨dI, ?_⟩
    calc
      rectangleDoubleCollarDualEdgeEmbedding a w h dI =
          rectanglePrimalDualEdgeEquiv (a.1, a.2 - 1) w (h + 2)
            (rectangleDoubleCollarPrimalEdgeEmbedding a w h f) := rfl
      _ = rectanglePrimalDualEdgeEquiv (a.1, a.2 - 1) w (h + 2) e.primalEdge :=
        congrArg (rectanglePrimalDualEdgeEquiv (a.1, a.2 - 1) w (h + 2)) hf
      _ = e := rectanglePrimalDualEdgeEquiv_apply_primalEdge_double e
  · rintro ⟨f, rfl⟩
    exact rectangleDoubleCollarDualEdgeEmbedding_mem a w h f

/-- The outer dual configuration marks as open exactly the edges crossing outer
primal edges outside the embedded inner primal carrier. This is a deletion
selector: those marked dual edges are deleted when forming the remaining graph;
they are not already closed in this selector configuration. -/
def rectangleDoubleCollarRemovedDualEdges (a : LatticeVertex) (w h : ℕ) :
    Configuration (rectangleDoubleCollarDualOuterGraph a w h) :=
  rectangleDualConfiguration (a.1, a.2 - 1) w (h + 2)
    (rectangleDoubleCollarInnerPrimalEdges a w h)

theorem rectangleDoubleCollar_pair_mem_open_iff
    (a : LatticeVertex) (w h : ℕ)
    (e : RectangleDualEdgeCarrier (a.1, a.2 - 1) w (h + 2)) :
    rectangleDualCarrierPair (a.1, a.2 - 1) w (h + 2) e ∈
      openEdges (rectangleDoubleCollarDualOuterGraph a w h)
        (rectangleDoubleCollarRemovedDualEdges a w h) ↔
      e.primalEdge ∉ rectangleDoubleCollarInnerPrimalEdges a w h := by
  have hval : (rectangleDualGraphEdgeEquiv (a.1, a.2 - 1) w (h + 2) e).val =
      rectangleDualCarrierPair (a.1, a.2 - 1) w (h + 2) e := rfl
  calc
    rectangleDualCarrierPair (a.1, a.2 - 1) w (h + 2) e ∈
        openEdges (rectangleDoubleCollarDualOuterGraph a w h)
          (rectangleDoubleCollarRemovedDualEdges a w h) ↔
      (rectangleDualGraphEdgeEquiv (a.1, a.2 - 1) w (h + 2) e).val ∈
        openEdges (rectangleDoubleCollarDualOuterGraph a w h)
          (rectangleDoubleCollarRemovedDualEdges a w h) := by rw [hval]
    _ ↔ rectangleDualGraphEdgeEquiv (a.1, a.2 - 1) w (h + 2) e ∈
        rectangleDoubleCollarRemovedDualEdges a w h := coe_mem_openEdges_iff _ _ _
    _ ↔ e.primalEdge ∉ rectangleDoubleCollarInnerPrimalEdges a w h :=
      mem_rectangleDualConfiguration _ _ _ _ _

/-- The graph obtained by deleting the selector's marked crossed-collar edges
retains the full expanded outer vertex carrier, including isolated vertices. -/
def rectangleDoubleCollarDualRemainingGraph (a : LatticeVertex) (w h : ℕ) :
    SimpleGraph (rectangleDoubleCollarDualOuterVertex a w h) :=
  edgeRestriction (rectangleDoubleCollarDualOuterGraph a w h)
    (rectangleDoubleCollarRemovedDualEdges a w h)

/-- Deleting exactly the selector-marked dual edges crossing the outer primal
collar leaves the actual inner dual graph embedded at the same coordinates in
the expanded outer carrier. This is a labelled-carrier graph identity, not a
full induced-graph claim. -/
theorem rectangleDoubleCollarDual_remainingGraph_eq_map_inner
    (a : LatticeVertex) (w h : ℕ) :
    rectangleDoubleCollarDualRemainingGraph a w h =
      (rectangleDoubleCollarDualInnerGraph a w h).map
        (rectangleDoubleCollarDual_vertexEmbedding a w h) := by
  ext u v
  rw [rectangleDoubleCollarDualRemainingGraph, edgeRestriction,
    SimpleGraph.deleteEdges_adj, SimpleGraph.map_adj]
  constructor
  · rintro ⟨hout, hnot⟩
    obtain ⟨e, hp⟩ := (rectangleDualGraph_adj_iff _ _ _ _ _).mp hout
    have hclosed : rectangleDualCarrierPair _ _ _ e ∉
        openEdges (rectangleDoubleCollarDualOuterGraph a w h)
          (rectangleDoubleCollarRemovedDualEdges a w h) := by
      simpa [hp] using hnot
    have heinner : e.primalEdge ∈ rectangleDoubleCollarInnerPrimalEdges a w h := by
      by_contra hbad
      exact hclosed ((rectangleDoubleCollar_pair_mem_open_iff a w h e).mpr hbad)
    obtain ⟨d, hd⟩ :=
      (rectangleDoubleCollarDualEdgeEmbedding_mem_iff a w h e).mp heinner
    have hpair := rectangleDoubleCollarDualEdgeEmbedding_pair a w h d
    have hpair' : s(u, v) = Sym2.map
        (rectangleDoubleCollarDual_vertexEmbedding a w h)
        (rectangleDualCarrierPair a w h d) := by
      calc
        s(u, v) = rectangleDualCarrierPair _ _ _ e := hp
        _ = rectangleDualCarrierPair _ _ _
            (rectangleDoubleCollarDualEdgeEmbedding a w h d) := by rw [hd]
        _ = Sym2.map (rectangleDoubleCollarDual_vertexEmbedding a w h)
            (rectangleDualCarrierPair a w h d) := hpair
    have hpair'' : s(u, v) = s(
        rectangleDoubleCollarDual_vertexEmbedding a w h (rectangleDualEdgeSource a w h d),
        rectangleDoubleCollarDual_vertexEmbedding a w h (rectangleDualEdgeTarget a w h d)) := by
      simpa [rectangleDualCarrierPair] using hpair'
    rcases Sym2.eq_iff.mp hpair'' with ⟨hu, hv⟩ | ⟨hu, hv⟩
    · exact ⟨rectangleDualEdgeSource a w h d, rectangleDualEdgeTarget a w h d,
        (rectangleDualGraph_adj_iff _ _ _ _ _).mpr ⟨d, rfl⟩, hu.symm, hv.symm⟩
    · exact ⟨rectangleDualEdgeTarget a w h d, rectangleDualEdgeSource a w h d,
        ((rectangleDualGraph_adj_iff _ _ _ _ _).mpr ⟨d, rfl⟩).symm, hu.symm, hv.symm⟩
  · rintro ⟨x, y, hinner, hxu, hyv⟩
    obtain ⟨d, hp⟩ := (rectangleDualGraph_adj_iff _ _ _ _ _).mp hinner
    have hpair : s(u, v) = rectangleDualCarrierPair _ _ _
        (rectangleDoubleCollarDualEdgeEmbedding a w h d) := by
      calc
        s(u, v) = s(rectangleDoubleCollarDual_vertexEmbedding a w h x,
            rectangleDoubleCollarDual_vertexEmbedding a w h y) := by rw [hxu, hyv]
        _ = Sym2.map (rectangleDoubleCollarDual_vertexEmbedding a w h) (s(x, y)) := rfl
        _ = Sym2.map (rectangleDoubleCollarDual_vertexEmbedding a w h)
            (rectangleDualCarrierPair a w h d) := congrArg _ hp
        _ = rectangleDualCarrierPair _ _ _
            (rectangleDoubleCollarDualEdgeEmbedding a w h d) :=
              (rectangleDoubleCollarDualEdgeEmbedding_pair a w h d).symm
    have hout : (rectangleDoubleCollarDualOuterGraph a w h).Adj u v :=
      (rectangleDualGraph_adj_iff _ _ _ _ _).mpr
        ⟨rectangleDoubleCollarDualEdgeEmbedding a w h d, hpair⟩
    refine ⟨hout, ?_⟩
    intro hopen
    have hopen' : rectangleDualCarrierPair _ _ _
        (rectangleDoubleCollarDualEdgeEmbedding a w h d) ∈
          openEdges (rectangleDoubleCollarDualOuterGraph a w h)
            (rectangleDoubleCollarRemovedDualEdges a w h) := by
      simpa [hpair] using hopen
    have hnotinner := (rectangleDoubleCollar_pair_mem_open_iff a w h
      (rectangleDoubleCollarDualEdgeEmbedding a w h d)).mp hopen'
    exact hnotinner
      (rectangleDoubleCollarDualEdgeEmbedding_mem a w h d)

end
end PottsContinuity.PlanarMixed.Square
