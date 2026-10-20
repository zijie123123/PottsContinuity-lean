-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/HorizontalStripIntervalCylinderRestriction.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.HorizontalStripIntervalCylinders
public import PottsContinuity.FKC.FiniteFK.HorizontalStripCutWindowInterval
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.FKC.Medial

open PottsContinuity.FKC.FiniteFK
open Finset

noncomputable section

local instance intervalRestrictionInnerEdgeFintype (n : ℕ) (lo hi : ℤ) :
    Fintype (rectangleGraph (lo, 0) (hi - lo).toNat (2 * n)).edgeSet := Fintype.ofFinite _
local instance intervalRestrictionOuterEdgeFintype (N n : ℕ) :
    Fintype (horizontalStripCutRectangle N n).edgeSet := Fintype.ofFinite _
local instance intervalRestrictionOuterEdgeDecidableEq (N n : ℕ) :
    DecidableEq (horizontalStripCutRectangle N n).edgeSet := Classical.decEq _

theorem horizontalStripCutWindowIntervalEdge_compatible {N n : ℕ} {lo hi : ℤ}
    (hlo : -(N : ℤ) ≤ lo) (hhi : hi ≤ N) (hle : lo ≤ hi)
    (e : (rectangleGraph (lo, 0) (hi - lo).toNat (2 * n)).edgeSet) :
    horizontalStripRectangleOriginalEdge N n
      (embeddedEdgeEmbedding (rectangleGraph (lo, 0) (hi - lo).toNat (2 * n))
        (horizontalStripCutRectangle N n)
        (horizontalStripCutWindowIntervalEmbedding hlo hhi hle)
        (horizontalStripCutWindowInterval_map_le hlo hhi hle) e) =
      rectanglePrimalEdgeToSquareEdge (lo, 0) (hi - lo).toNat (2 * n) e := by
  apply Subtype.ext
  change Sym2.map (fun v : RectangleVertex (-(N : ℤ), 0) (2 * N) (2 * n) => v.val)
      (Sym2.map (horizontalStripCutWindowIntervalEmbedding hlo hhi hle) e.val) =
    Sym2.map (fun v : RectangleVertex (lo, 0) (hi - lo).toNat (2 * n) => v.val) e.val
  rw [Sym2.map_map]
  congr 1

theorem horizontalStripCutWindowIntervalCylinder_restrict_iff
    {N n : ℕ} {lo hi : ℤ} (hlo : -(N : ℤ) ≤ lo) (hhi : hi ≤ N)
    (hle : lo ≤ hi) (F : Finset squareLattice.edgeSet)
    (hF : ∀ e ∈ F, e ∈ Set.range
      (rectanglePrimalEdgeToSquareEdge (lo, 0) (hi - lo).toNat (2 * n)))
    (A : Configuration (horizontalStripCutRectangle N n)) :
    A ∈ horizontalStripRectangleCylinderEvent N n F ↔
      embeddedConfigurationRestriction
        (rectangleGraph (lo, 0) (hi - lo).toNat (2 * n))
        (horizontalStripCutRectangle N n)
        (horizontalStripCutWindowIntervalEmbedding hlo hhi hle)
        (horizontalStripCutWindowInterval_map_le hlo hhi hle) A ∈
          horizontalStripIntervalCylinderEvent lo (hi - lo).toNat n F := by
  constructor
  · intro hA
    change F ⊆ A.image (horizontalStripRectangleOriginalEdge N n) at hA
    intro e he
    obtain ⟨x, hxe⟩ := Set.mem_range.mp (hF e he)
    have heOpen : e ∈ A.image (horizontalStripRectangleOriginalEdge N n) := hA he
    obtain ⟨y, hy, hye⟩ := Finset.mem_image.mp heOpen
    have hcompat := horizontalStripCutWindowIntervalEdge_compatible hlo hhi hle x
    have hyx : embeddedEdgeEmbedding
        (rectangleGraph (lo, 0) (hi - lo).toNat (2 * n))
        (horizontalStripCutRectangle N n)
        (horizontalStripCutWindowIntervalEmbedding hlo hhi hle)
        (horizontalStripCutWindowInterval_map_le hlo hhi hle) x = y := by
      apply horizontalStripRectangleOriginalEdge_injective N n
      calc
        horizontalStripRectangleOriginalEdge N n
            (embeddedEdgeEmbedding
              (rectangleGraph (lo, 0) (hi - lo).toNat (2 * n))
              (horizontalStripCutRectangle N n)
              (horizontalStripCutWindowIntervalEmbedding hlo hhi hle)
              (horizontalStripCutWindowInterval_map_le hlo hhi hle) x) =
            rectanglePrimalEdgeToSquareEdge (lo, 0) (hi - lo).toNat (2 * n) x := hcompat
        _ = e := hxe
        _ = horizontalStripRectangleOriginalEdge N n y := hye.symm
    have hxA : embeddedEdgeEmbedding
        (rectangleGraph (lo, 0) (hi - lo).toNat (2 * n))
        (horizontalStripCutRectangle N n)
        (horizontalStripCutWindowIntervalEmbedding hlo hhi hle)
        (horizontalStripCutWindowInterval_map_le hlo hhi hle) x ∈ A := by
      rw [hyx]
      exact hy
    have hxRestriction : x ∈ embeddedConfigurationRestriction
        (rectangleGraph (lo, 0) (hi - lo).toNat (2 * n))
        (horizontalStripCutRectangle N n)
        (horizontalStripCutWindowIntervalEmbedding hlo hhi hle)
        (horizontalStripCutWindowInterval_map_le hlo hhi hle) A :=
      (mem_embeddedConfigurationRestriction _ _ _ _ A x).mpr hxA
    exact Finset.mem_image.mpr ⟨x, hxRestriction, hxe⟩
  · intro hA
    change F ⊆
      (embeddedConfigurationRestriction
        (rectangleGraph (lo, 0) (hi - lo).toNat (2 * n))
        (horizontalStripCutRectangle N n)
        (horizontalStripCutWindowIntervalEmbedding hlo hhi hle)
        (horizontalStripCutWindowInterval_map_le hlo hhi hle) A).image
        (rectanglePrimalEdgeToSquareEdge (lo, 0) (hi - lo).toNat (2 * n)) at hA
    intro e he
    obtain ⟨x, hxRestriction, hxe⟩ := Finset.mem_image.mp (hA he)
    have hxA : embeddedEdgeEmbedding
        (rectangleGraph (lo, 0) (hi - lo).toNat (2 * n))
        (horizontalStripCutRectangle N n)
        (horizontalStripCutWindowIntervalEmbedding hlo hhi hle)
        (horizontalStripCutWindowInterval_map_le hlo hhi hle) x ∈ A :=
      (mem_embeddedConfigurationRestriction _ _ _ _ A x).mp hxRestriction
    exact Finset.mem_image.mpr ⟨
      embeddedEdgeEmbedding
        (rectangleGraph (lo, 0) (hi - lo).toNat (2 * n))
        (horizontalStripCutRectangle N n)
        (horizontalStripCutWindowIntervalEmbedding hlo hhi hle)
        (horizontalStripCutWindowInterval_map_le hlo hhi hle) x,
      hxA,
      (horizontalStripCutWindowIntervalEdge_compatible hlo hhi hle x).trans hxe⟩

end
end PottsContinuity.FKC.Medial
