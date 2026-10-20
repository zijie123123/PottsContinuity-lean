module

public import PottsContinuity.Thm4Plane.ScreenMixedFactor
public import PottsContinuity.PlanarMixed.SourceActiveCrosscutComparison

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

local instance activeConnectorEdgeDecidableEq (m : ℕ) :
    DecidableEq
      (PottsContinuity.FKC.FiniteFK.slitBoxGraph (16 * m)).edgeSet :=
  Classical.decEq _

local instance activeConnectorConfigurationMeasurableSpace (m : ℕ) :
    MeasurableSpace (Configuration
      (PottsContinuity.FKC.FiniteFK.slitBoxGraph (16 * m))) :=
  PottsContinuity.PD.FK.configurationMeasurableSpace _

def slitScreenRStarActiveGraph (m : ℕ)
    (D : VerticalSquareCrosscutData (slitScreenRStarBase m)
      (slitScreenRStarSide m)) :=
  PottsContinuity.PD.FK.edgeRestriction
    (rankedBandGraph
      (rectangleGraph (slitScreenRStarBase m)
        (slitScreenRStarSide m) (slitScreenRStarSide m)) D.rank)
    (bandArcBonds _ D.rank)

def slitScreenRStarActiveArcs (m : ℕ)
    (D : VerticalSquareCrosscutData (slitScreenRStarBase m)
      (slitScreenRStarSide m)) : Set (Configuration (slitScreenRStarActiveGraph m D)) :=
  PottsContinuity.BD12.arcsConnectionEvent (slitScreenRStarActiveGraph m D)
    {z | z.val ∈ D.first.support} {z | z.val ∈ D.second.support}

structure SlitActiveConnectorRecordInput
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
  crosscut : ∀ X, stoppingObservationMap reveal X ∈ T →
    VerticalSquareCrosscutData (slitScreenRStarBase m)
      (slitScreenRStarSide m)
  residual : ∀ X (hsel : stoppingObservationMap reveal X ∈ T),
    PottsContinuity.PD.FK.RemainingConfiguration
      (PottsContinuity.FKC.FiniteFK.slitBoxGraph (16 * m)) (reveal X) →
      Configuration (slitScreenRStarActiveGraph m (crosscut X hsel))
  hlaw : ∀ X (hsel : stoppingObservationMap reveal X ∈ T),
    (remainingLaw (PottsContinuity.FKC.FiniteFK.slitBoxGraph (16 * m))
      (criticalParameters (⟨q, q.2.1⟩ : Set.Ici (1 : ℝ)))
      (frozenBoundary
        (PottsContinuity.Thm4.fkcBoundaryToPD
          (PottsContinuity.FKC.FiniteFK.slitBoxBoundary (16 * m)))
        (revealRecordConfiguration reveal X).val)
      (reveal X)).map (residual X hsel) =
      law (slitScreenRStarActiveGraph m (crosscut X hsel))
        (criticalParameters (⟨q, q.2.1⟩ : Set.Ici (1 : ℝ)))
        (rankedBandBoundary (crosscut X hsel).rank)
  hsurgery : ∀ X (hsel : stoppingObservationMap reveal X ∈ T),
    ∀ Y ∈ revealRecordEvent reveal X,
      (PottsContinuity.PD.FK.configurationSplitEquiv
        (PottsContinuity.FKC.FiniteFK.slitBoxGraph (16 * m))
        (reveal X) Y).1 ∈
          (residual X hsel) ⁻¹' slitScreenRStarActiveArcs m
            (crosscut X hsel) →
        Y ∈ slitScreenEvent m ∩
          (PottsContinuity.FKC.FiniteFK.slitScreenLeftCrossingEvent m ∩
            PottsContinuity.FKC.FiniteFK.slitScreenRightCrossingEvent m) ∩
            slitScreenConnectorEvent m

end
end PottsContinuity.Thm4Plane
