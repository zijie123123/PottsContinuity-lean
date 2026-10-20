-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/HorizontalStripClosedCutCylinderSupport.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.HorizontalStripClosedCutExploration
public import PottsContinuity.FKC.FiniteFK.HorizontalStripCutWindowInterval
public import PottsContinuity.FKC.FiniteFK.HorizontalStripIntervalCylinderRestriction
public import PottsContinuity.FKC.FiniteFK.RectangleDualCarrier
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.FKC.Medial

open PottsContinuity.FKC.FiniteFK
open Finset

noncomputable section

local instance closedCutCylinderOuterEdgeFintype (N n : ℕ) :
    Fintype (horizontalStripCutRectangle N n).edgeSet := Fintype.ofFinite _
local instance closedCutCylinderCenterEdgeFintype (K n : ℕ) :
    Fintype (rectangleGraph (-(K : ℤ), 0) (2 * K) (2 * n)).edgeSet := Fintype.ofFinite _
local instance closedCutCylinderIntervalEdgeFintype (n : ℕ) (lo hi : ℤ) :
    Fintype (rectangleGraph (lo, 0) (hi - lo).toNat (2 * n)).edgeSet := Fintype.ofFinite _
local instance closedCutCylinderOuterEdgeDecidableEq (N n : ℕ) :
    DecidableEq (horizontalStripCutRectangle N n).edgeSet := Classical.decEq _

private theorem horizontalStripRectangleOriginalEdge_eq_rectanglePrimalEdge
    (K n : ℕ) (e : (horizontalStripCutRectangle K n).edgeSet) :
    horizontalStripRectangleOriginalEdge K n e =
      rectanglePrimalEdgeToSquareEdge (-(K : ℤ), 0) (2 * K) (2 * n) e := by
  apply Subtype.ext
  rw [horizontalStripRectangleOriginalEdge_val]
  rfl

theorem horizontalStripClosedCut_cylinder_edge_support
    {N n K : ℕ} (hKN : K ≤ N) {i j : ℕ}
    (A : Finset (horizontalStripCutRectangle N n).edgeSet)
    (hL : (horizontalStripLeftBlockScan N n K A).2 = some i)
    (hR : (horizontalStripRightBlockScan N n K A).2 = some j)
    (F : Finset squareLattice.edgeSet)
    (hF : ∀ e ∈ F, e ∈ Set.range (horizontalStripRectangleOriginalEdge K n)) :
    ∀ e ∈ F,
      e ∈ Set.range (rectanglePrimalEdgeToSquareEdge
        (-(N : ℤ) + (i : ℤ) + 1, 0)
        ((N : ℤ) - 1 - (j : ℤ) - (-(N : ℤ) + (i : ℤ) + 1)).toNat
        (2 * n)) := by
  have hcenter := horizontalStripClosedCutReveal_window_contains_center
    N n K A hKN hL hR
  rcases hcenter with ⟨hlo, hhi⟩
  let lo : ℤ := -(N : ℤ) + (i : ℤ) + 1
  let hi : ℤ := (N : ℤ) - 1 - (j : ℤ)
  let w : ℕ := (hi - lo).toNat
  have hlo' : lo ≤ -(K : ℤ) := by dsimp [lo]; exact hlo
  have hhi' : (K : ℤ) ≤ hi := by dsimp [hi]; exact hhi
  have hlohi : lo ≤ hi := by dsimp [lo, hi]; omega
  have hrect : latticeRectangle (-(K : ℤ), 0) (2 * K) (2 * n) ⊆
      latticeRectangle (lo, 0) w (2 * n) := by
    intro v hv
    rw [mem_latticeRectangle] at hv ⊢
    rcases hv with ⟨⟨hxlo, hxhi⟩, hy⟩
    constructor
    · constructor
      · omega
      · have hw : (w : ℤ) = hi - lo := by
          dsimp [w]
          rw [Int.toNat_of_nonneg (sub_nonneg.mpr hlohi)]
        have hKUpper : -(K : ℤ) + (2 * K : ℕ) = (K : ℤ) := by omega
        omega
    · exact hy
  let f := rectangleVertexEmbedding hrect
  have hmap : (rectangleGraph (-(K : ℤ), 0) (2 * K) (2 * n)).map f ≤
      rectangleGraph (lo, 0) w (2 * n) :=
    rectangleGraph_map_rectangleVertexEmbedding hrect
  intro e he
  obtain ⟨e₀, he₀⟩ := Set.mem_range.mp (hF e he)
  let e₁ : (rectangleGraph (lo, 0) w (2 * n)).edgeSet := rectangleEdgeEmbedding hrect e₀
  have hcompat : rectanglePrimalEdgeToSquareEdge (lo, 0) w (2 * n) e₁ =
      rectanglePrimalEdgeToSquareEdge (-(K : ℤ), 0) (2 * K) (2 * n) e₀ := by
    apply Subtype.ext
    exact rectangleEdgeEmbedding_original hrect e₀
  refine ⟨e₁, ?_⟩
  calc
    rectanglePrimalEdgeToSquareEdge (lo, 0) w (2 * n) e₁ =
        rectanglePrimalEdgeToSquareEdge (-(K : ℤ), 0) (2 * K) (2 * n) e₀ := hcompat
    _ = horizontalStripRectangleOriginalEdge K n e₀ :=
      (horizontalStripRectangleOriginalEdge_eq_rectanglePrimalEdge K n e₀).symm
    _ = e := he₀

end
end PottsContinuity.FKC.Medial
