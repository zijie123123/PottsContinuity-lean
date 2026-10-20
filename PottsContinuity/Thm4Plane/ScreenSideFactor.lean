module

public import PottsContinuity.Thm4Plane.ScreenFactorAssembly
public import PottsContinuity.Thm3.RSW.StoppedConnection
public import PottsContinuity.Thm3.RSW.StoppingAverage
public import PottsContinuity.Thm3.RSW.PushConditional
public import PottsContinuity.Thm3.RSW.FiniteBoundary

/-!
# The two side screens from recordwise rotated crossing estimates

Each record input describes one application of Lemma 3 in a finite residual
domain.  Its map to the slit-screen carrier and its actual-path inclusion are
kept explicit.  The stopped-record disintegration of `Thm3.RSW.StoppingAverage` then
turns those local estimates into the two joint side-screen factors.
-/

@[expose] public section

namespace PottsContinuity.Thm4Plane

open MeasureTheory
open PottsContinuity.PD.FK
open PottsContinuity.Exploration
open PottsContinuity.RSW

noncomputable section

attribute [local instance] configurationMeasurableSpace remainingConfigurationMeasurableSpace

local instance screenPushEdgeDecidableEq (m : ℕ) :
    DecidableEq (PottsContinuity.FKC.FiniteFK.slitBoxGraph (16 * m)).edgeSet :=
  Classical.decEq _

local instance screenPushConfigurationMeasurableSpace (m : ℕ) :
    MeasurableSpace (Configuration
      (PottsContinuity.FKC.FiniteFK.slitBoxGraph (16 * m))) :=
  PottsContinuity.PD.FK.configurationMeasurableSpace _

/-- The fixed rectangle obtained by rotating the right (or reflected left)
side screen at source scale `n = 16*m`. Its width parameter is `k=4`, its
height parameter is `ell=15/4`, and the Lemma-3 crossing scale is `4*m`. -/
noncomputable def slitRotatedPushRectangle (m : ℕ) : Finset (ℤ × ℤ) :=
  PottsContinuity.RSW.topWiredRectangle 4 (15 / 4) (4 * m)

/-- The actual frozen horizontal crossing of height `4*m` in the rotated
top-wired rectangle. This is the local event used by the Lemma 3 estimate. -/
def slitRotatedPushCrossingEvent (m : ℕ) : Set (Configuration
    (PottsContinuity.squareLattice.induce
      (slitRotatedPushRectangle m : Set (ℤ × ℤ)))) :=
  PottsContinuity.RSW.finiteBoolEvent (slitRotatedPushRectangle m)
    (PottsContinuity.horizontalCrossing (slitRotatedPushRectangle m)
      (-⌊(4 : ℝ) * (4 * m)⌋) ⌊(4 : ℝ) * (4 * m)⌋ 0 (4 * m))

/-- Data for one stopped-record application of the rotated true-dual
rectangle crossing estimate.  The local event is the literal horizontal
crossing of the `k=4`, `ell=15/4`, `n=4*m` rectangle of Lemma 3.  The residual-law map,
boundary order, and actual-path implication transport the canonical Lemma-3
bound to `target` on the original slit-box carrier.
-/
structure SlitRotatedPushRecordInput (q : Set.Icc (1 : ℝ) 4) (m : ℕ)
    (selected target : Set (Configuration
      (PottsContinuity.FKC.FiniteFK.slitBoxGraph (16 * m)))) where
  reveal : RevealMap
    (G := PottsContinuity.FKC.FiniteFK.slitBoxGraph (16 * m))
  hstable : ∀ X X', X' ∩ reveal X = X ∩ reveal X → reveal X' = reveal X
  T : Set (StoppingObservationRange reveal)
  hselected : (stoppingObservationMap reveal) ⁻¹' T = selected
  η : (X : Configuration
    (PottsContinuity.FKC.FiniteFK.slitBoxGraph (16 * m))) →
      BoundaryCondition (slitRotatedPushRectangle m : Set (ℤ × ℤ))
  r : (X : Configuration
    (PottsContinuity.FKC.FiniteFK.slitBoxGraph (16 * m))) →
      RemainingConfiguration
        (PottsContinuity.FKC.FiniteFK.slitBoxGraph (16 * m))
        (reveal X) → Configuration
          (PottsContinuity.squareLattice.induce
            (slitRotatedPushRectangle m : Set (ℤ × ℤ)))
  hlaw : ∀ X, stoppingObservationMap reveal X ∈ T →
    (remainingLaw
      (PottsContinuity.FKC.FiniteFK.slitBoxGraph (16 * m))
      (PottsContinuity.Thm4.selfDualParameters
        (⟨q, q.2.1⟩ : Set.Ici (1 : ℝ)))
      (frozenBoundary
        (PottsContinuity.Thm4.fkcBoundaryToPD
          (PottsContinuity.FKC.FiniteFK.slitBoxBoundary (16 * m)))
        (revealRecordConfiguration reveal X).val)
      (reveal X)).map (r X) =
      law (PottsContinuity.squareLattice.induce
        (slitRotatedPushRectangle m : Set (ℤ × ℤ)))
        (PottsContinuity.Thm4.selfDualParameters
          (⟨q, q.2.1⟩ : Set.Ici (1 : ℝ)))
        (η X)
  hboundary : ∀ X, stoppingObservationMap reveal X ∈ T →
    (PottsContinuity.RSW.topWiredRectangleBoundary
      4 (15 / 4) (4 * m)).partition ≤ (η X).partition
  htarget : ∀ X, stoppingObservationMap reveal X ∈ T →
    ∀ Y ∈ revealRecordEvent reveal X,
      (configurationSplitEquiv
        (PottsContinuity.FKC.FiniteFK.slitBoxGraph (16 * m))
        (reveal X) Y).1 ∈ (r X) ⁻¹' slitRotatedPushCrossingEvent m →
      Y ∈ target

end
end PottsContinuity.Thm4Plane
