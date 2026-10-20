/- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
accessible (see `related_formalizations` in formalization.yaml): file
`FiniteFK/GeneralRectangleDualBottomCollar.lean`.
Adaptation: namespace/import relocation; reuse existing PD/BD12 carriers.
Independent interior edge probability and every real q>=1 (PD.FK.Parameters).
No upper bound q<4 is used in this finite proof. -/
module

public import PottsContinuity.PD.Duality.RectangleDualCarrier
public import PottsContinuity.PD.FK.BoundaryPartitionLaw
public import PottsContinuity.PlanarMixed.Square.GeneralRectangleBottomCollar
public import PottsContinuity.PD.Duality.RectangleFlowDimension
public import PottsContinuity.PlanarMixed.Square.Extras
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Basic

@[expose] public section

namespace PottsContinuity.PlanarMixed.Square
open PD.FK PD.FK.Medial PD.Duality BD12
open scoped PottsContinuity.PlanarMixed.Square

open PD.FK PD.FK.Medial

noncomputable section

abbrev generalRectangleDualBottomCollarInnerGraph (a : LatticeVertex) (w h : ℕ) :=
  rectangleDualGraph a w h

abbrev generalRectangleDualBottomCollarOuterGraph (a : LatticeVertex) (w h : ℕ) :=
  rectangleDualGraph (a.1, a.2 - 1) w (h + 1)

abbrev generalRectangleDualBottomCollarInnerVertex (a : LatticeVertex) (w h : ℕ) :=
  RectangleDualVertex a w h

abbrev generalRectangleDualBottomCollarOuterVertex (a : LatticeVertex) (w h : ℕ) :=
  RectangleDualVertex (a.1, a.2 - 1) w (h + 1)

/-- The expanded face-base rectangle embeds under a one-row downward collar. -/
theorem generalRectangleDualBottomCollar_vertex_subset (a : LatticeVertex) (w h : ℕ) :
    rectangleDualExpanded a w h ⊆
      rectangleDualExpanded (a.1, a.2 - 1) w (h + 1) := by
  intro z hz
  rw [rectangleDualExpanded, mem_latticeRectangle] at hz ⊢
  rcases hz with ⟨⟨hx₁, hx₂⟩, ⟨hy₁, hy₂⟩⟩
  exact ⟨⟨hx₁, hx₂⟩, ⟨by omega, by omega⟩⟩

def generalRectangleDualBottomCollar_vertexEmbedding (a : LatticeVertex) (w h : ℕ) :
    generalRectangleDualBottomCollarInnerVertex a w h ↪
      generalRectangleDualBottomCollarOuterVertex a w h :=
  ⟨fun v => ⟨v.val, generalRectangleDualBottomCollar_vertex_subset a w h v.property⟩,
    fun x y hxy => by
      have hv : x.val = y.val :=
        congrArg (fun z : generalRectangleDualBottomCollarOuterVertex a w h => z.val) hxy
      exact Subtype.ext hv⟩

@[simp] theorem generalRectangleDualBottomCollar_vertexEmbedding_val
    (a : LatticeVertex) (w h : ℕ)
    (v : generalRectangleDualBottomCollarInnerVertex a w h) :
    (generalRectangleDualBottomCollar_vertexEmbedding a w h v).val = v.val := rfl

theorem generalRectangleDualBottomCollar_primal_subset (a : LatticeVertex) (w h : ℕ) :
    latticeRectangle a w h ⊆ latticeRectangle (a.1, a.2 - 1) w (h + 1) := by
  exact rectangleArbitraryBottomCollar_subset a w h

def generalRectangleDualBottomCollar_primalEdgeEmbedding (a : LatticeVertex) (w h : ℕ) :
    rectanglePrimalEdgeCarrier a w h ↪
      rectanglePrimalEdgeCarrier (a.1, a.2 - 1) w (h + 1) :=
  rectangleEdgeEmbedding (generalRectangleDualBottomCollar_primal_subset a w h)

theorem generalRectangleDualBottomCollar_primalBond_eq (a : LatticeVertex) (w h : ℕ)
    (e : rectanglePrimalEdgeCarrier a w h) :
    rectanglePrimalEdgeBond (a.1, a.2 - 1) w (h + 1)
        (generalRectangleDualBottomCollar_primalEdgeEmbedding a w h e) =
      rectanglePrimalEdgeBond a w h e := by
  apply LatticeBond.toSym2_injective
  rw [rectanglePrimalEdgeBond_toSym2_public, rectanglePrimalEdgeBond_toSym2_public]
  exact rectangleEdgeEmbedding_original (generalRectangleDualBottomCollar_primal_subset a w h) e

def generalRectangleDualBottomCollar_dualEdgeEmbedding (a : LatticeVertex) (w h : ℕ) :
    RectangleDualEdgeCarrier a w h ↪
      RectangleDualEdgeCarrier (a.1, a.2 - 1) w (h + 1) := by
  let eI := rectanglePrimalDualEdgeEquiv a w h
  let eO := rectanglePrimalDualEdgeEquiv (a.1, a.2 - 1) w (h + 1)
  exact ⟨fun d => eO (generalRectangleDualBottomCollar_primalEdgeEmbedding a w h (eI.symm d)), by
    intro d d' hd
    apply eI.symm.injective
    apply (generalRectangleDualBottomCollar_primalEdgeEmbedding a w h).injective
    exact eO.injective hd⟩

@[simp] theorem generalRectangleDualBottomCollar_dualEdgeEmbedding_primalEdge
    (a : LatticeVertex) (w h : ℕ) (e : RectangleDualEdgeCarrier a w h) :
    (generalRectangleDualBottomCollar_dualEdgeEmbedding a w h e).primalEdge =
      generalRectangleDualBottomCollar_primalEdgeEmbedding a w h e.primalEdge := rfl

/-- The actual dual edge endpoints commute with the literal expanded-vertex embedding. -/
theorem generalRectangleDualBottomCollar_dualEdgeEmbedding_pair
    (a : LatticeVertex) (w h : ℕ) (e : RectangleDualEdgeCarrier a w h) :
    rectangleDualCarrierPair (a.1, a.2 - 1) w (h + 1)
        (generalRectangleDualBottomCollar_dualEdgeEmbedding a w h e) =
      Sym2.map (generalRectangleDualBottomCollar_vertexEmbedding a w h)
        (rectangleDualCarrierPair a w h e) := by
  apply Sym2.eq_iff.mpr
  left
  constructor
  · apply Subtype.ext
    simp only [generalRectangleDualBottomCollar_vertexEmbedding_val]
    calc
      (rectangleDualEdgeSource _ _ _
          (generalRectangleDualBottomCollar_dualEdgeEmbedding a w h e)).val =
          (rectanglePrimalEdgeBond _ _ _
            (generalRectangleDualBottomCollar_primalEdgeEmbedding a w h e.primalEdge)).faceBase false :=
        rectangleDualEdgeSource_faceBase _ _ _ _
      _ = (rectanglePrimalEdgeBond a w h e.primalEdge).faceBase false := by
        rw [generalRectangleDualBottomCollar_primalBond_eq]
      _ = (rectangleDualEdgeSource a w h e).val :=
        (rectangleDualEdgeSource_faceBase _ _ _ _).symm
  · apply Subtype.ext
    simp only [generalRectangleDualBottomCollar_vertexEmbedding_val]
    calc
      (rectangleDualEdgeTarget _ _ _
          (generalRectangleDualBottomCollar_dualEdgeEmbedding a w h e)).val =
          (rectanglePrimalEdgeBond _ _ _
            (generalRectangleDualBottomCollar_primalEdgeEmbedding a w h e.primalEdge)).faceBase true :=
        rectangleDualEdgeTarget_faceBase _ _ _ _
      _ = (rectanglePrimalEdgeBond a w h e.primalEdge).faceBase true := by
        rw [generalRectangleDualBottomCollar_primalBond_eq]
      _ = (rectangleDualEdgeTarget a w h e).val :=
        (rectangleDualEdgeTarget_faceBase _ _ _ _).symm

end
end PottsContinuity.PlanarMixed.Square
