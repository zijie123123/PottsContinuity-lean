/- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
accessible (see `related_formalizations` in formalization.yaml): file
`FiniteFK/RectangleDoubleCollarDualEdges.lean`.
Adaptation: namespace/import relocation; reuse existing PD/BD12 carriers.
Independent interior edge probability and every real q>=1 (PD.FK.Parameters).
No upper bound q<4 is used in this finite proof. -/
module

public import PottsContinuity.PlanarMixed.Square.RectangleDoubleCollar
public import PottsContinuity.PlanarMixed.Square.RectangleDoubleCollarDualBoundary
public import PottsContinuity.PD.Duality.RectangleDualConfiguration
public import PottsContinuity.PlanarMixed.Square.Extras
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Maps

@[expose] public section

namespace PottsContinuity.PlanarMixed.Square
open PD.FK PD.FK.Medial PD.Duality BD12
open scoped PottsContinuity.PlanarMixed.Square

open PD.FK PD.FK.Medial

noncomputable section

abbrev rectangleDoubleCollarDualInnerGraph (a : LatticeVertex) (w h : ℕ) :=
  rectangleDualGraph a w h

abbrev rectangleDoubleCollarDualOuterGraph (a : LatticeVertex) (w h : ℕ) :=
  rectangleDualGraph (a.1, a.2 - 1) w (h + 2)

def rectangleDoubleCollarPrimalEdgeEmbedding (a : LatticeVertex) (w h : ℕ) :
    rectanglePrimalEdgeCarrier a w h ↪
      rectanglePrimalEdgeCarrier (a.1, a.2 - 1) w (h + 2) :=
  rectangleEdgeEmbedding (rectangleDoubleCollar_vertex_inclusion a w h)

theorem rectangleDoubleCollar_primalBond_eq (a : LatticeVertex) (w h : ℕ)
    (e : rectanglePrimalEdgeCarrier a w h) :
    rectanglePrimalEdgeBond (a.1, a.2 - 1) w (h + 2)
      (rectangleDoubleCollarPrimalEdgeEmbedding a w h e) =
      rectanglePrimalEdgeBond a w h e := by
  apply LatticeBond.toSym2_injective
  rw [rectanglePrimalEdgeBond_toSym2_public, rectanglePrimalEdgeBond_toSym2_public]
  exact rectangleEdgeEmbedding_original (rectangleDoubleCollar_vertex_inclusion a w h) e

/-- The dual edge embedding retains each original primal edge label, conjugated
by the rectangle primal-dual equivalences. -/
def rectangleDoubleCollarDualEdgeEmbedding (a : LatticeVertex) (w h : ℕ) :
    RectangleDualEdgeCarrier a w h ↪
      RectangleDualEdgeCarrier (a.1, a.2 - 1) w (h + 2) := by
  let eI := rectanglePrimalDualEdgeEquiv a w h
  let eO := rectanglePrimalDualEdgeEquiv (a.1, a.2 - 1) w (h + 2)
  exact ⟨fun d => eO (rectangleDoubleCollarPrimalEdgeEmbedding a w h (eI.symm d)), by
    intro d d' hdd'
    apply eI.symm.injective
    apply (rectangleDoubleCollarPrimalEdgeEmbedding a w h).injective
    exact eO.injective hdd'⟩

@[simp] theorem rectangleDoubleCollarDualEdgeEmbedding_primalEdge
    (a : LatticeVertex) (w h : ℕ) (e : RectangleDualEdgeCarrier a w h) :
    (rectangleDoubleCollarDualEdgeEmbedding a w h e).primalEdge =
      rectangleDoubleCollarPrimalEdgeEmbedding a w h e.primalEdge := rfl

/-- The labelled inner and outer dual edge carriers commute with the literal
same-coordinate expanded-vertex embedding. -/
theorem rectangleDoubleCollarDualEdgeEmbedding_pair
    (a : LatticeVertex) (w h : ℕ) (e : RectangleDualEdgeCarrier a w h) :
    rectangleDualCarrierPair (a.1, a.2 - 1) w (h + 2)
        (rectangleDoubleCollarDualEdgeEmbedding a w h e) =
      Sym2.map (rectangleDoubleCollarDual_vertexEmbedding a w h)
        (rectangleDualCarrierPair a w h e) := by
  apply Sym2.eq_iff.mpr
  left
  constructor
  · apply Subtype.ext
    simp only [rectangleDoubleCollarDual_vertexEmbedding_val]
    calc
      (rectangleDualEdgeSource _ _ _ (rectangleDoubleCollarDualEdgeEmbedding a w h e)).val =
          (rectanglePrimalEdgeBond _ _ _
            (rectangleDoubleCollarPrimalEdgeEmbedding a w h e.primalEdge)).faceBase false :=
        rectangleDualEdgeSource_faceBase _ _ _ _
      _ = (rectanglePrimalEdgeBond a w h e.primalEdge).faceBase false := by
        rw [rectangleDoubleCollar_primalBond_eq]
      _ = (rectangleDualEdgeSource a w h e).val :=
        (rectangleDualEdgeSource_faceBase _ _ _ _).symm
  · apply Subtype.ext
    simp only [rectangleDoubleCollarDual_vertexEmbedding_val]
    calc
      (rectangleDualEdgeTarget _ _ _ (rectangleDoubleCollarDualEdgeEmbedding a w h e)).val =
          (rectanglePrimalEdgeBond _ _ _
            (rectangleDoubleCollarPrimalEdgeEmbedding a w h e.primalEdge)).faceBase true :=
        rectangleDualEdgeTarget_faceBase _ _ _ _
      _ = (rectanglePrimalEdgeBond a w h e.primalEdge).faceBase true := by
        rw [rectangleDoubleCollar_primalBond_eq]
      _ = (rectangleDualEdgeTarget a w h e).val :=
        (rectangleDualEdgeTarget_faceBase _ _ _ _).symm

/-- The actual inner expanded dual graph embeds into the outer dual graph.
This is an inclusion of its labelled carrier edges, not an assertion that the
dual graph is the full induced square-lattice graph. -/
theorem rectangleDoubleCollarDual_map_le (a : LatticeVertex) (w h : ℕ) :
    (rectangleDoubleCollarDualInnerGraph a w h).map
      (rectangleDoubleCollarDual_vertexEmbedding a w h) ≤
      rectangleDoubleCollarDualOuterGraph a w h := by
  intro u v huv
  rcases (SimpleGraph.map_adj (rectangleDoubleCollarDual_vertexEmbedding a w h)
      (rectangleDoubleCollarDualInnerGraph a w h) u v).mp huv with
    ⟨x, y, hxy, rfl, rfl⟩
  rcases (rectangleDualGraph_adj_iff a w h x y).mp hxy with ⟨e, he⟩
  have hpair := rectangleDoubleCollarDualEdgeEmbedding_pair a w h e
  have hmapped :
      s(rectangleDoubleCollarDual_vertexEmbedding a w h x,
        rectangleDoubleCollarDual_vertexEmbedding a w h y) =
        rectangleDualCarrierPair (a.1, a.2 - 1) w (h + 2)
          (rectangleDoubleCollarDualEdgeEmbedding a w h e) := by
    calc
      s(rectangleDoubleCollarDual_vertexEmbedding a w h x,
        rectangleDoubleCollarDual_vertexEmbedding a w h y) =
          Sym2.map (rectangleDoubleCollarDual_vertexEmbedding a w h) (s(x,y)) := rfl
      _ = Sym2.map (rectangleDoubleCollarDual_vertexEmbedding a w h)
          (rectangleDualCarrierPair a w h e) := congrArg _ he
      _ = rectangleDualCarrierPair (a.1, a.2 - 1) w (h + 2)
          (rectangleDoubleCollarDualEdgeEmbedding a w h e) := hpair.symm
  exact (rectangleDualGraph_adj_iff (a.1, a.2 - 1) w (h + 2) _ _).mpr
    ⟨rectangleDoubleCollarDualEdgeEmbedding a w h e, hmapped⟩

end
end PottsContinuity.PlanarMixed.Square
