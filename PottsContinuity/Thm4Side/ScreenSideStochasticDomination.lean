module

public import PottsContinuity.Thm4Side.ScreenSideSelection
public import PottsContinuity.Thm4Plane.ScreenSideFactor
public import PottsContinuity.Thm3.Push.PushOfStripRSW

@[expose] public section

namespace PottsContinuity.Thm4Side

open MeasureTheory
open PottsContinuity.PD.FK
open PottsContinuity.Exploration
open PottsContinuity.RSW
open PottsContinuity.Thm4Plane

noncomputable section

attribute [local instance] configurationMeasurableSpace remainingConfigurationMeasurableSpace

local instance sideDomEdgeDecidableEq (m : ℕ) :
    DecidableEq (PottsContinuity.FKC.FiniteFK.slitBoxGraph (16 * m)).edgeSet :=
  Classical.decEq _

local instance sideDomTargetMeasurableSpace (m : ℕ) :
    MeasurableSpace (Configuration
      (PottsContinuity.squareLattice.induce
        (slitRotatedPushRectangle m : Set (ℤ × ℤ)))) :=
  configurationMeasurableSpace _

/-- A side record with conditional stochastic domination of the canonical
rotated top-wired law.  It is the probability-level input needed by the Lemma 3
side-screen estimate when the exact rectangle graph isomorphism in
`SlitRotatedPushRecordInput` is unavailable. -/
structure SlitRotatedPushDomRecordInput (q : Set.Icc (1 : ℝ) 4) (m : ℕ)
    (selected target : Set (Configuration
      (PottsContinuity.FKC.FiniteFK.slitBoxGraph (16 * m)))) where
  reveal : RevealMap (G := PottsContinuity.FKC.FiniteFK.slitBoxGraph (16 * m))
  hstable : ∀ X X', X' ∩ reveal X = X ∩ reveal X → reveal X' = reveal X
  T : Set (StoppingObservationRange reveal)
  hselected : (stoppingObservationMap reveal) ⁻¹' T = selected
  r : (X : Configuration
      (PottsContinuity.FKC.FiniteFK.slitBoxGraph (16 * m))) →
    RemainingConfiguration
      (PottsContinuity.FKC.FiniteFK.slitBoxGraph (16 * m)) (reveal X) →
      Configuration (PottsContinuity.squareLattice.induce
        (slitRotatedPushRectangle m : Set (ℤ × ℤ)))
  hstoch : ∀ X, stoppingObservationMap reveal X ∈ T →
    ∀ U : Set (Configuration
      (PottsContinuity.squareLattice.induce
        (slitRotatedPushRectangle m : Set (ℤ × ℤ)))),
      IsUpperSet U →
      (law (PottsContinuity.squareLattice.induce
          (slitRotatedPushRectangle m : Set (ℤ × ℤ)))
        (selfDualParameters (⟨q, q.2.1⟩ : Set.Ici (1 : ℝ)))
        (topWiredRectangleBoundary 4 (15 / 4) (4 * m))).toMeasure U ≤
      (remainingLaw (PottsContinuity.FKC.FiniteFK.slitBoxGraph (16 * m))
        (selfDualParameters (⟨q, q.2.1⟩ : Set.Ici (1 : ℝ)))
        (frozenBoundary
          (PottsContinuity.Thm4.fkcBoundaryToPD
            (PottsContinuity.FKC.FiniteFK.slitBoxBoundary (16 * m)))
          (revealRecordConfiguration reveal X).val)
        (reveal X)).toMeasure
        ((r X) ⁻¹' U)
  htarget : ∀ X, stoppingObservationMap reveal X ∈ T →
    ∀ Y ∈ revealRecordEvent reveal X,
      (configurationSplitEquiv
        (PottsContinuity.FKC.FiniteFK.slitBoxGraph (16 * m))
        (reveal X) Y).1 ∈
          (r X) ⁻¹' slitRotatedPushCrossingEvent m →
        Y ∈ target

end
end PottsContinuity.Thm4Side
