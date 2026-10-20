module

public import PottsContinuity.Thm3.Push.RectangleCarrierInclusion
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Basic

@[expose] public section

namespace PottsContinuity.Push
open PottsContinuity.PD.FK
noncomputable section

/-- Restricting an actual true-dual label cut to an inner primal rectangle
is exactly the cut of the restricted label. Expanded face coordinates and
original bond states commute with the SAME literal inclusion. -/
theorem rectangle_labelCut_restriction {a b : LatticeVertex} {w h W H : ℕ}
    (hrect : PD.FK.latticeRectangle a w h ⊆ PD.FK.latticeRectangle b W H)
    (hdual : rectangleDualExpanded a w h ⊆ rectangleDualExpanded b W H)
    (σ : RectangleDualVertex b W H → Bool) :
    auxiliaryLabelCut (DualityExt.rectangleDualEdgeEquiv a w h)
      (σ ∘ rectangleDualVertexEmbedding hdual) =
    DualityExt.rectangleConfigurationRestriction hrect
      (auxiliaryLabelCut (DualityExt.rectangleDualEdgeEquiv b W H) σ) := by
  classical
  ext f
  rw [DualityExt.rectangleConfigurationRestriction,mem_embeddedConfigurationRestriction]
  let g := embeddedEdgeEmbedding _ _ (DualityExt.rectangleVertexEmbedding hrect)
    (DualityExt.rectangleGraph_map_rectangleVertexEmbedding hrect) f
  let d := rectanglePrimalDualEdgeEquiv a w h f
  let D := rectanglePrimalDualEdgeEquiv b W H g
  have hends := rectangleDualEndpoints_embedded hrect hdual f
  rw [mem_auxiliaryLabelCut_iff _ _ f (rectangleDualEdgeSource a w h d)
    (rectangleDualEdgeTarget a w h d) (by rfl),
    mem_auxiliaryLabelCut_iff _ _ g (rectangleDualEdgeSource b W H D)
      (rectangleDualEdgeTarget b W H D) (by rfl)]
  change σ (rectangleDualVertexEmbedding hdual (rectangleDualEdgeSource a w h d)) ≠
    σ (rectangleDualVertexEmbedding hdual (rectangleDualEdgeTarget a w h d)) ↔ _
  rw [hends.1,hends.2]

/-- An auxiliary-region reveal can be read directly from the two actual
endpoints of the complementary bond. -/
theorem mem_auxiliaryRegionReveal_iff_endpoints {V Z : Type*} [Finite V]
    {G : SimpleGraph V} {K : SimpleGraph Z} (e : G.edgeSet ≃ K.edgeSet)
    (S : Set Z) (f : G.edgeSet) (u v : Z) (hf : (e f).val=s(u,v)) :
    f ∈ auxiliaryRegionReveal e S ↔ u ∈ S ∨ v ∈ S := by
  rw [mem_auxiliaryRegionReveal,hf]
  constructor
  · rintro ⟨t,ht,htS⟩
    rcases (Sym2.mem_iff').mp ht with rfl | rfl
    · exact Or.inl htS
    · exact Or.inr htS
  · rintro (hu | hv)
    · exact ⟨u,(Sym2.mem_iff').mpr (Or.inl rfl),hu⟩
    · exact ⟨v,(Sym2.mem_iff').mpr (Or.inr rfl),hv⟩

/-- Reveals based on actual true-dual endpoint membership also commute with
restriction to a contained rectangle. This retains recorded CLOSED states. -/
theorem rectangle_regionReveal_restriction {a b : LatticeVertex} {w h W H : ℕ}
    (hrect : PD.FK.latticeRectangle a w h ⊆ PD.FK.latticeRectangle b W H)
    (hdual : rectangleDualExpanded a w h ⊆ rectangleDualExpanded b W H)
    (S : Set (RectangleDualVertex b W H)) :
    auxiliaryRegionReveal (DualityExt.rectangleDualEdgeEquiv a w h)
      (rectangleDualVertexEmbedding hdual ⁻¹' S) =
    DualityExt.rectangleConfigurationRestriction hrect
      (auxiliaryRegionReveal (DualityExt.rectangleDualEdgeEquiv b W H) S) := by
  classical
  ext f
  rw [DualityExt.rectangleConfigurationRestriction,mem_embeddedConfigurationRestriction]
  let g := embeddedEdgeEmbedding _ _ (DualityExt.rectangleVertexEmbedding hrect)
    (DualityExt.rectangleGraph_map_rectangleVertexEmbedding hrect) f
  let d := rectanglePrimalDualEdgeEquiv a w h f
  let D := rectanglePrimalDualEdgeEquiv b W H g
  have hends := rectangleDualEndpoints_embedded hrect hdual f
  rw [mem_auxiliaryRegionReveal_iff_endpoints _ _ f (rectangleDualEdgeSource a w h d)
    (rectangleDualEdgeTarget a w h d) (by rfl),
    mem_auxiliaryRegionReveal_iff_endpoints _ _ g (rectangleDualEdgeSource b W H D)
      (rectangleDualEdgeTarget b W H D) (by rfl)]
  change (rectangleDualVertexEmbedding hdual (rectangleDualEdgeSource a w h d) ∈ S ∨
    rectangleDualVertexEmbedding hdual (rectangleDualEdgeTarget a w h d) ∈ S) ↔ _
  rw [hends.1,hends.2]

end
end PottsContinuity.Push
