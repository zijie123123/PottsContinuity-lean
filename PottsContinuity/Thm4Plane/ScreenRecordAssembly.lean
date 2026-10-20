module

public import PottsContinuity.Thm4Plane.ScreenPlaneAssembly
public import PottsContinuity.Thm4Plane.ScreenMixedFactor
public import PottsContinuity.Thm4Plane.PlaneFiniteComparison
public import PottsContinuity.Thm4Plane.ScreenFactorAssembly
public import PottsContinuity.Thm3.RSW.StoppingAverage
public import PottsContinuity.Thm3.RSW.StoppingUpper
public import PottsContinuity.PlanarMixed.OmegaConditional
public import PottsContinuity.PD.FK.RemainingComparison
public import Mathlib.Tactic
public import PottsContinuity.Exploration.FiniteStoppingSetDMP

@[expose] public section

namespace PottsContinuity.Thm4Plane

open MeasureTheory
open PottsContinuity.PD.FK
open PottsContinuity.Exploration
open PottsContinuity.RSW
open PottsContinuity.PlanarMixed

noncomputable section

attribute [local instance] configurationMeasurableSpace remainingConfigurationMeasurableSpace

local instance screenRecordEdgeDecidableEq (m : ℕ) :
    DecidableEq (PottsContinuity.FKC.FiniteFK.slitBoxGraph (16 * m)).edgeSet :=
  Classical.decEq _

local instance screenRecordConfigurationMeasurableSpace (m : ℕ) :
    MeasurableSpace (Configuration
      (PottsContinuity.FKC.FiniteFK.slitBoxGraph (16 * m))) :=
  PottsContinuity.PD.FK.configurationMeasurableSpace _

/-- Record data sufficient to derive the source connector factor from the
mixed-boundary square estimate of `PlanarMixed.Square` on each selected residual
domain. These fields describe the actual selected records, their induced two-arc
domain, the exact residual law, and the path surgery back to the slit event. -/
structure SlitConnectorRecordInput (q : Set.Icc (1 : ℝ) 4) (m : ℕ) where
  a : LatticeVertex
  N : ℕ
  hN : 1 ≤ N
  reveal : RevealMap
    (G := PottsContinuity.FKC.FiniteFK.slitBoxGraph (16 * m))
  hstable : ∀ X X', X' ∩ reveal X = X ∩ reveal X → reveal X' = reveal X
  T : Set (StoppingObservationRange reveal)
  hT : (stoppingObservationMap reveal) ⁻¹' T =
    slitScreenEvent m ∩
      (PottsContinuity.FKC.FiniteFK.slitScreenLeftCrossingEvent m ∩
        PottsContinuity.FKC.FiniteFK.slitScreenRightCrossingEvent m)
  V : Type*
  [instFiniteV : Finite V]
  Ω : Configuration
    (PottsContinuity.FKC.FiniteFK.slitBoxGraph (16 * m)) → SimpleGraph V
  f : V ↪ RectangleVertex a N N
  A : Configuration
    (PottsContinuity.FKC.FiniteFK.slitBoxGraph (16 * m)) → Set V
  C : Configuration
    (PottsContinuity.FKC.FiniteFK.slitBoxGraph (16 * m)) → Set V
  η : Configuration
    (PottsContinuity.FKC.FiniteFK.slitBoxGraph (16 * m)) → BoundaryCondition V
  hΩ : ∀ X, stoppingObservationMap reveal X ∈ T →
    (Ω X).map f ≤ rectangleGraph a N N
  hboundary : ∀ X, stoppingObservationMap reveal X ∈ T →
    ExtremalBoundaryComparison a N hN (Ω X) f (η X)
  hpaths : ∀ X (hsel : stoppingObservationMap reveal X ∈ T),
    SquareCrossingRestrictsToArcs a N (Ω X) f (hΩ X hsel) (A X) (C X)
  r : ∀ X, RemainingConfiguration
    (PottsContinuity.FKC.FiniteFK.slitBoxGraph (16 * m))
    (reveal X) → Configuration (Ω X)
  hlaw : ∀ X, stoppingObservationMap reveal X ∈ T →
    (remainingLaw
      (PottsContinuity.FKC.FiniteFK.slitBoxGraph (16 * m))
      (criticalParameters (⟨q, q.2.1⟩ : Set.Ici (1 : ℝ)))
      (frozenBoundary
        (PottsContinuity.Thm4.fkcBoundaryToPD
          (PottsContinuity.FKC.FiniteFK.slitBoxBoundary (16 * m)))
        (revealRecordConfiguration reveal X).val)
      (reveal X)).map (r X) =
      law (Ω X) (criticalParameters (⟨q, q.2.1⟩ : Set.Ici (1 : ℝ)))
        (η X)
  hsurgery : ∀ X, stoppingObservationMap reveal X ∈ T →
    ∀ Y ∈ revealRecordEvent reveal X,
      (configurationSplitEquiv
        (PottsContinuity.FKC.FiniteFK.slitBoxGraph (16 * m))
        (reveal X) Y).1 ∈
          (r X) ⁻¹' PottsContinuity.BD12.arcsConnectionEvent
            (Ω X) (A X) (C X) →
        Y ∈ slitScreenEvent m ∩
          (PottsContinuity.FKC.FiniteFK.slitScreenLeftCrossingEvent m ∩
            PottsContinuity.FKC.FiniteFK.slitScreenRightCrossingEvent m) ∩
              slitScreenConnectorEvent m

/-- Record data sufficient to compare the selected connector event with the
free plane law. The event inclusion, upper-set property, exact free residual
law and path containment are fields; no probability comparison is assumed. -/
structure SlitPlaneRecordInput
    (q : Set.Icc (1 : ℝ) 4) (m : ℕ)
    (p : Set.Icc (0 : ℝ) 1)
    (μ : Measure (PottsContinuity.squareLattice.edgeSet → Bool))
    (hp : (p : ℝ) = Real.sqrt q / (1 + Real.sqrt q)) where
  reveal : RevealMap
    (G := PottsContinuity.FKC.FiniteFK.slitBoxGraph (16 * m))
  hstable : ∀ X X', X' ∩ reveal X = X ∩ reveal X → reveal X' = reveal X
  T : Set (StoppingObservationRange reveal)
  hT : (stoppingObservationMap reveal) ⁻¹' T =
    slitScreenEvent m ∩
      (PottsContinuity.FKC.FiniteFK.slitScreenLeftCrossingEvent m ∩
        PottsContinuity.FKC.FiniteFK.slitScreenRightCrossingEvent m)
  V : Type*
  [instFiniteV : Finite V]
  Ω : Configuration
    (PottsContinuity.FKC.FiniteFK.slitBoxGraph (16 * m)) → SimpleGraph V
  f : V ↪ LatticeVertex
  A : (X : Configuration
    (PottsContinuity.FKC.FiniteFK.slitBoxGraph (16 * m))) →
      Set (Configuration (Ω X))
  r : ∀ X, RemainingConfiguration
    (PottsContinuity.FKC.FiniteFK.slitBoxGraph (16 * m))
    (reveal X) → Configuration (Ω X)
  hgraph : ∀ X, stoppingObservationMap reveal X ∈ T →
    (Ω X).map f ≤ PottsContinuity.PD.FK.squareLattice
  hupper : ∀ X, IsUpperSet (A X)
  hinclude : ∀ X (hsel : stoppingObservationMap reveal X ∈ T),
    PottsContinuity.Infinite.latticeGraphEvent
      (Ω X) f (hgraph X hsel) (A X) ⊆
        translatedBoxBoundaryConnectionEvent (0, -(16 * (m : ℤ))) m
  hfreeLaw : ∀ X, stoppingObservationMap reveal X ∈ T →
    (remainingLaw
      (PottsContinuity.FKC.FiniteFK.slitBoxGraph (16 * m))
      (criticalParameters (⟨q, q.2.1⟩ : Set.Ici (1 : ℝ)))
      (frozenBoundary
        (PottsContinuity.Thm4.fkcBoundaryToPD
          (PottsContinuity.FKC.FiniteFK.slitBoxBoundary (16 * m)))
        (revealRecordConfiguration reveal X).val)
      (reveal X)).map (r X) =
    law (Ω X)
      (PottsContinuity.Infinite.pdParameters p
        ⟨q, lt_of_lt_of_le one_pos q.2.1⟩
        (by
          rw [hp]
          exact div_pos
            (Real.sqrt_pos.2 (lt_of_lt_of_le zero_lt_one q.2.1))
            (by positivity))
        (by
          rw [hp]
          have hs : 0 < Real.sqrt (q : ℝ) := Real.sqrt_pos.2
            (lt_of_lt_of_le zero_lt_one q.2.1)
          exact (div_lt_one (by positivity)).2 (by linarith))
        q.2.1)
      (BoundaryCondition.free ∅)
  hsourcePath : ∀ X, stoppingObservationMap reveal X ∈ T →
    ∀ Y ∈ revealRecordEvent reveal X,
      Y ∈ slitScreenEvent m ∩
        (PottsContinuity.FKC.FiniteFK.slitScreenLeftCrossingEvent m ∩
          PottsContinuity.FKC.FiniteFK.slitScreenRightCrossingEvent m) ∩
            slitScreenConnectorEvent m →
      (configurationSplitEquiv
        (PottsContinuity.FKC.FiniteFK.slitBoxGraph (16 * m))
        (reveal X) Y).1 ∈ (r X) ⁻¹' A X

end
end PottsContinuity.Thm4Plane
