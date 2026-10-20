module

public import PottsContinuity.Thm3.RSW.BottomCollarInnerMarginal
public import PottsContinuity.Thm3.Push.BottomCoreLaw

@[expose] public section

namespace PottsContinuity.RSW
open PD.FK PD.Duality PlanarMixed.Square
noncomputable section

/-- Read the actual retained core sample, first discarding isolated host
vertices and then integrating the original free bottom leaves. -/
def bottomCollarCoreRestriction (a : LatticeVertex) (w h : ℕ)
    (D : Configuration (bottomCollarInducedDualGraph a w h)) :
    Configuration (generalRectangleDualBottomCoreGraph a w h) :=
  embeddedConfigurationRestriction (generalRectangleDualBottomCoreGraph a w h)
    (rectangleDualGraph a w h) (Push.bottomCoreInclusion a w h) (Push.bottomCoreGraph_map_le a w h)
    (embeddedConfigurationRestriction (rectangleDualGraph a w h)
      (bottomCollarInducedDualGraph a w h)
      (generalRectangleDualBottomCollar_vertexEmbedding a w h) (bottomCollar_inner_map_le a w h) D)

/-- Exact retained-core marginal of the actual complementary sampled graph,
for every admissible FK parameter and the literal exterior partition. -/
theorem bottomCollar_core_law_map (a : LatticeVertex) (w h : ℕ) (θ : Parameters) :
    (law (bottomCollarInducedDualGraph a w h) θ
      (rectangleDualBoundaryCondition (a.1,a.2-1) w (h+1))).map
      (bottomCollarCoreRestriction a w h) =
    law (generalRectangleDualBottomCoreGraph a w h) θ
      (BoundaryCondition.wired {u : generalRectangleDualBottomCoreVertex a w h |
        Push.bottomCoreInclusion a w h u ∈ generalRectangleDualBottomCollarInnerThreeSides a w h}) := by
  change (law _ _ _).map (_ ∘ _) = _
  rw [← PMF.map_comp,bottomCollar_inner_law_map]
  exact Push.bottomCore_law_map a w h θ

end
end PottsContinuity.RSW
