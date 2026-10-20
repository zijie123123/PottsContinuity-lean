module

public import PottsContinuity.Thm4Plane.ScreenActiveConnectorFactor
public import PottsContinuity.PlanarMixed.SourceCrosscutShapes

@[expose] public section

namespace PottsContinuity.Thm4Plane

open MeasureTheory
open PottsContinuity.PD.FK
open PottsContinuity.Exploration
open PottsContinuity.RSW
open PottsContinuity.PlanarMixed
open PottsContinuity.BD12

noncomputable section

attribute [local instance] PottsContinuity.PD.FK.configurationMeasurableSpace
  PottsContinuity.PD.FK.remainingConfigurationMeasurableSpace

local instance activeConnectorPathsEdgeDecidableEq (m : ℕ) :
    DecidableEq
      (PottsContinuity.FKC.FiniteFK.slitBoxGraph (16 * m)).edgeSet :=
  Classical.decEq _

local instance activeConnectorPathsConfigurationMeasurableSpace (m : ℕ) :
    MeasurableSpace (Configuration
      (PottsContinuity.FKC.FiniteFK.slitBoxGraph (16 * m))) :=
  PottsContinuity.PD.FK.configurationMeasurableSpace _

/-- The actual left and right source paths in the fixed dual square R*. -/
structure SlitScreenRStarSourcePathPair (m : ℕ) where
  C : Configuration (rectangleGraph (slitScreenRStarBase m)
    (slitScreenRStarSide m) (slitScreenRStarSide m))
  u : RectangleVertex (slitScreenRStarBase m)
    (slitScreenRStarSide m) (slitScreenRStarSide m)
  v : RectangleVertex (slitScreenRStarBase m)
    (slitScreenRStarSide m) (slitScreenRStarSide m)
  s : RectangleVertex (slitScreenRStarBase m)
    (slitScreenRStarSide m) (slitScreenRStarSide m)
  t : RectangleVertex (slitScreenRStarBase m)
    (slitScreenRStarSide m) (slitScreenRStarSide m)
  leftPath : (openGraph (rectangleGraph (slitScreenRStarBase m)
    (slitScreenRStarSide m) (slitScreenRStarSide m)) C).Walk u v
  rightPath : (openGraph (rectangleGraph (slitScreenRStarBase m)
    (slitScreenRStarSide m) (slitScreenRStarSide m)) C).Walk s t
  leftBottom : u.val.2 = -(12 * (m : ℤ))
  rightBottom : s.val.2 = -(12 * (m : ℤ))
  leftTop : v.val.2 = -(12 * (m : ℤ)) + (slitScreenRStarSide m : ℕ)
  rightTop : t.val.2 = -(12 * (m : ℤ)) + (slitScreenRStarSide m : ℕ)
  leftOfMiddle : ∀ z ∈ leftPath.support,
    z.val.1 ≤ -(m : ℤ) - 1
  rightOfMiddle : ∀ z ∈ rightPath.support,
    (m : ℤ) ≤ z.val.1

/-- The crosscut construction `generalCCrosscutData` turns the selected source paths into
the ranked crosscut data. -/
def SlitScreenRStarSourcePathPair.crosscutData (m : ℕ)
    (d : SlitScreenRStarSourcePathPair m) :
    VerticalSquareCrosscutData (slitScreenRStarBase m)
      (slitScreenRStarSide m) :=
  generalCCrosscutData m d.C d.leftPath d.rightPath
    d.leftBottom d.rightBottom d.leftTop d.rightTop
    d.leftOfMiddle d.rightOfMiddle

/-- A connector record stated using its selected source paths, with the
crosscut geometry of `PlanarMixed.SourceCrosscutShapes` derived internally. -/
structure SlitActiveConnectorSourcePathRecordInput
    (q : Set.Icc (1 : ℝ) 4) (m : ℕ) where
  reveal : RevealMap
    (G := PottsContinuity.FKC.FiniteFK.slitBoxGraph (16 * m))
  hstable : ∀ X X', X' ∩ reveal X = X ∩ reveal X →
    reveal X' = reveal X
  T : Set (StoppingObservationRange reveal)
  hT : (stoppingObservationMap reveal) ⁻¹' T =
    slitScreenEvent m ∩
      (PottsContinuity.FKC.FiniteFK.slitScreenLeftCrossingEvent m ∩
        PottsContinuity.FKC.FiniteFK.slitScreenRightCrossingEvent m)
  paths : ∀ X, stoppingObservationMap reveal X ∈ T →
    SlitScreenRStarSourcePathPair m
  residual : ∀ X (hsel : stoppingObservationMap reveal X ∈ T),
    RemainingConfiguration
      (PottsContinuity.FKC.FiniteFK.slitBoxGraph (16 * m))
      (reveal X) →
    Configuration
      (slitScreenRStarActiveGraph m ((paths X hsel).crosscutData m))
  hlaw : ∀ X (hsel : stoppingObservationMap reveal X ∈ T),
    (remainingLaw
      (PottsContinuity.FKC.FiniteFK.slitBoxGraph (16 * m))
      (criticalParameters (⟨q, q.2.1⟩ : Set.Ici (1 : ℝ)))
      (frozenBoundary
        (PottsContinuity.Thm4.fkcBoundaryToPD
          (PottsContinuity.FKC.FiniteFK.slitBoxBoundary (16 * m)))
        (revealRecordConfiguration reveal X).val)
      (reveal X)).map (residual X hsel) =
      law
        (slitScreenRStarActiveGraph m ((paths X hsel).crosscutData m))
        (criticalParameters (⟨q, q.2.1⟩ : Set.Ici (1 : ℝ)))
        (rankedBandBoundary ((paths X hsel).crosscutData m).rank)
  hsurgery : ∀ X (hsel : stoppingObservationMap reveal X ∈ T),
    ∀ Y ∈ revealRecordEvent reveal X,
      (PottsContinuity.PD.FK.configurationSplitEquiv
        (PottsContinuity.FKC.FiniteFK.slitBoxGraph (16 * m))
        (reveal X) Y).1 ∈
          (residual X hsel) ⁻¹' slitScreenRStarActiveArcs m
            ((paths X hsel).crosscutData m) →
        Y ∈ slitScreenEvent m ∩
          (PottsContinuity.FKC.FiniteFK.slitScreenLeftCrossingEvent m ∩
            PottsContinuity.FKC.FiniteFK.slitScreenRightCrossingEvent m) ∩
            slitScreenConnectorEvent m

end
end PottsContinuity.Thm4Plane
