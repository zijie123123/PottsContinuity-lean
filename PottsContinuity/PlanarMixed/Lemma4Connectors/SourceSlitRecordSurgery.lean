module

public import PottsContinuity.Thm4Plane.ScreenActiveConnectorDualConfig
public import PottsContinuity.PlanarMixed.EmbeddedOpenRestriction

@[expose] public section

namespace PottsContinuity.PlanarMixed.Lemma4Connectors
open PD.FK BD12 Thm4Plane Exploration RSW
noncomputable section

/-- Full actual source paths and literal support inclusion of their R* crops.
There is no connector, clipping, or boundary-comparison conclusion in this data. -/
structure SlitSourceScreenCropWitness (m : ℕ)
    (A : Configuration (FKC.FiniteFK.slitBoxGraph (16*m)))
    (d : SlitScreenRStarSourcePathPair m) where
  lb : FKC.LatticeVertex
  lt : FKC.LatticeVertex
  rb : FKC.LatticeVertex
  rt : FKC.LatticeVertex
  leftBottom : lb ∈ FKC.FiniteFK.slitScreenBottomTerminals m (FKC.FiniteFK.slitScreenLeftFaceBases m)
  leftTop : lt ∈ FKC.FiniteFK.slitScreenTopTerminals m (FKC.FiniteFK.slitScreenLeftFaceBases m)
  rightBottom : rb ∈ FKC.FiniteFK.slitScreenBottomTerminals m (FKC.FiniteFK.slitScreenRightFaceBases m)
  rightTop : rt ∈ FKC.FiniteFK.slitScreenTopTerminals m (FKC.FiniteFK.slitScreenRightFaceBases m)
  left : (FKC.FiniteFK.slitScreenActualConfigurationClosedDualGraph m A
    (FKC.FiniteFK.slitScreenLeftFaceBases m)).Walk lb lt
  right : (FKC.FiniteFK.slitScreenActualConfigurationClosedDualGraph m A
    (FKC.FiniteFK.slitScreenRightFaceBases m)).Walk rb rt
  leftCrop : ∀ u ∈ d.leftPath.support, u.val ∈ left.support
  rightCrop : ∀ v ∈ d.rightPath.support, v.val ∈ right.support

local instance sourceSlitRecordEdgeEq (m : ℕ) :
    DecidableEq (FKC.FiniteFK.slitBoxGraph (16*m)).edgeSet := Classical.decEq _

end
end PottsContinuity.PlanarMixed.Lemma4Connectors
