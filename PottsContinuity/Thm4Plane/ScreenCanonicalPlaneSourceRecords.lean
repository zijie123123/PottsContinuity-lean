module

public import PottsContinuity.Thm4Plane.ScreenRecordAssembly
public import PottsContinuity.Thm4Plane.ScreenCapFullCarrierEvent
public import PottsContinuity.Thm4Plane.ScreenCapComplementFreeLaw

@[expose] public section

namespace PottsContinuity.Thm4Plane

open MeasureTheory
open PottsContinuity.PD.FK
open PottsContinuity.FKC.FiniteFK
open PottsContinuity.Exploration
open PottsContinuity.Infinite
open PottsContinuity.RSW

noncomputable section

attribute [local instance] PottsContinuity.PD.FK.configurationMeasurableSpace
  PottsContinuity.PD.FK.remainingConfigurationMeasurableSpace

abbrev ScreenSlitConfiguration (m : ℕ) :=
  PottsContinuity.FKC.FiniteFK.Configuration (slitBoxGraph (16 * m))

local instance canonicalPlaneSourceEdgeDecidableEq (m : ℕ) :
    DecidableEq (slitBoxGraph (16 * m)).edgeSet := Classical.decEq _

local instance canonicalPlaneSourceConfigurationMeasurableSpace (m : ℕ) :
    MeasurableSpace (ScreenSlitConfiguration m) :=
  PottsContinuity.PD.FK.configurationMeasurableSpace _

local instance canonicalPlaneSourceFullCarrierEdgeFintype (m : ℕ)
    (R : ScreenSlitConfiguration m)
    (D : Set (SlitBoxVertex (16 * m))) :
    Fintype (screenCapEdgeDeletedFullCarrierGraph m R D).edgeSet :=
  Fintype.ofFinite _

def slitScreenPlaneJointSourceEvent (m : ℕ) :
    Set (ScreenSlitConfiguration m) :=
  slitScreenEvent m ∩
    (PottsContinuity.FKC.FiniteFK.slitScreenLeftCrossingEvent m ∩
      PottsContinuity.FKC.FiniteFK.slitScreenRightCrossingEvent m)

/-- A selected source dual arch with its two bottom endpoints. -/
structure SlitScreenPlaneSourceArch (m : ℕ)
    (X : ScreenSlitConfiguration m) where
  lb : PottsContinuity.FKC.LatticeVertex
  rb : PottsContinuity.FKC.LatticeVertex
  leftBottom : lb ∈ generalScreenBottomTerminals (16 * m)
    (generalScreenLeftFaceBases (16 * m))
  rightBottom : rb ∈ generalScreenBottomTerminals (16 * m)
    (generalScreenRightFaceBases (16 * m))
  dualWalk : (generalScreenActualClosedDualGraph (16 * m) X
    (generalScreenArchFaceBases (16 * m))).Walk lb rb
  isPath : dualWalk.IsPath

noncomputable def slitScreenPlaneSourceCut (m : ℕ)
    (select : ∀ X, X ∈ slitScreenPlaneJointSourceEvent m →
      SlitScreenPlaneSourceArch m X)
    (X : ScreenSlitConfiguration m) : ScreenSlitConfiguration m := by
  classical
  exact if hX : X ∈ slitScreenPlaneJointSourceEvent m then
    screenArchCrossedBondConfiguration m X (select X hX).dualWalk
  else ∅

noncomputable def slitScreenPlaneSourceCap (m : ℕ)
    (select : ∀ X, X ∈ slitScreenPlaneJointSourceEvent m →
      SlitScreenPlaneSourceArch m X)
    (X : ScreenSlitConfiguration m) : Set (SlitBoxVertex (16 * m)) :=
  screenTargetCapEdgeDeletedComponent m (slitScreenPlaneSourceCut m select X)

noncomputable def slitScreenPlaneSourceReveal (m : ℕ)
    (select : ∀ X, X ∈ slitScreenPlaneJointSourceEvent m →
      SlitScreenPlaneSourceArch m X) :
    RevealMap (G := slitBoxGraph (16 * m)) :=
  fun X => screenCapComplementReveal m
    (slitScreenPlaneSourceCut m select X)
    (slitScreenPlaneSourceCap m select X) X

noncomputable def slitScreenPlaneSourceGraph (m : ℕ)
    (select : ∀ X, X ∈ slitScreenPlaneJointSourceEvent m →
      SlitScreenPlaneSourceArch m X)
    (X : ScreenSlitConfiguration m) : SimpleGraph (SlitBoxVertex (16 * m)) :=
  screenCapEdgeDeletedFullCarrierGraph m
    (slitScreenPlaneSourceCut m select X)
    (slitScreenPlaneSourceCap m select X)

noncomputable def slitScreenPlaneSourceCapEvent (m : ℕ)
    (select : ∀ X, X ∈ slitScreenPlaneJointSourceEvent m →
      SlitScreenPlaneSourceArch m X)
    (hm : 1 ≤ m) (X : ScreenSlitConfiguration m) :
    Set (PottsContinuity.PD.FK.Configuration
      (slitScreenPlaneSourceGraph m select X)) := by
  classical
  exact if hX : X ∈ slitScreenPlaneJointSourceEvent m then
    screenCapFullCarrierBoundaryConnectionEvent m
      (slitScreenPlaneSourceCut m select X)
      (slitScreenPlaneSourceCap m select X)
      (screenTargetCap_subset_edgeDeletedComponent_of_no_internal_removal
        m hm (slitScreenPlaneSourceCut m select X)
        (by
          simpa [slitScreenPlaneSourceCut, hX] using
            screenArchCrossedBondConfiguration_avoids_capInternalEdge_of_exteriorSupport
              m X (select X hX).dualWalk
              (generalScreenArchWalk_support_outsideTargetBox m hm X
                (select X hX).dualWalk (select X hX).leftBottom)))
  else ∅

noncomputable def slitScreenPlaneSourceDecoder (m : ℕ)
    (select : ∀ X, X ∈ slitScreenPlaneJointSourceEvent m →
      SlitScreenPlaneSourceArch m X)
    (X : ScreenSlitConfiguration m) :
    PottsContinuity.PD.FK.RemainingConfiguration
      (slitBoxGraph (16 * m)) (slitScreenPlaneSourceReveal m select X) →
    PottsContinuity.PD.FK.Configuration
      (slitScreenPlaneSourceGraph m select X) :=
  screenCapComplementRevealFullCarrierDecoder m
    (slitScreenPlaneSourceCut m select X)
    (slitScreenPlaneSourceCap m select X) X

/-- Canonical plane records for the stopped exploration. The fixed-carrier graph,
its plane embedding, the increasing cap event, and the plane-event inclusion are
derived from the selected bottom arch. The exact stopped-record free law and source
event transfer remain explicit selector data. -/
structure SlitCanonicalPlaneSourceArchRecordInput
    (q : Set.Icc (1 : ℝ) 4) (m : ℕ)
    (p : Set.Icc (0 : ℝ) 1)
    (μ : Measure (PottsContinuity.squareLattice.edgeSet → Bool))
    (hp : (p : ℝ) = Real.sqrt q / (1 + Real.sqrt q)) where
  select : ∀ X, X ∈ slitScreenPlaneJointSourceEvent m →
    SlitScreenPlaneSourceArch m X
  positive : 1 ≤ m
  T : Set (StoppingObservationRange (slitScreenPlaneSourceReveal m select))
  stable : ∀ X X', X' ∩ slitScreenPlaneSourceReveal m select X =
      X ∩ slitScreenPlaneSourceReveal m select X →
      slitScreenPlaneSourceReveal m select X' =
        slitScreenPlaneSourceReveal m select X
  observation :
    (stoppingObservationMap (slitScreenPlaneSourceReveal m select)) ⁻¹' T =
      slitScreenPlaneJointSourceEvent m
  freeLaw : ∀ X,
    stoppingObservationMap (slitScreenPlaneSourceReveal m select) X ∈ T →
    (remainingLaw
      (slitBoxGraph (16 * m))
      (criticalParameters (⟨q, q.2.1⟩ : Set.Ici (1 : ℝ)))
      (frozenBoundary
        (PottsContinuity.Thm4.fkcBoundaryToPD
          (PottsContinuity.FKC.FiniteFK.slitBoxBoundary (16 * m)))
        (revealRecordConfiguration (slitScreenPlaneSourceReveal m select) X).val)
      (slitScreenPlaneSourceReveal m select X)).map
      (slitScreenPlaneSourceDecoder m select X) =
    law (slitScreenPlaneSourceGraph m select X)
      (PottsContinuity.Infinite.pdParameters p
        ⟨q, lt_of_lt_of_le one_pos q.2.1⟩
        (by
          rw [hp]
          exact div_pos
            (Real.sqrt_pos.2 (lt_of_lt_of_le zero_lt_one q.2.1))
            (by positivity))
        (by
          rw [hp]
          have hs : 0 < Real.sqrt (q : ℝ) :=
            Real.sqrt_pos.2 (lt_of_lt_of_le zero_lt_one q.2.1)
          exact (div_lt_one (by positivity)).2 (by linarith))
        q.2.1)
      (BoundaryCondition.free ∅)
  sourceEvent : ∀ X,
    stoppingObservationMap (slitScreenPlaneSourceReveal m select) X ∈ T →
    ∀ Y ∈ revealRecordEvent (slitScreenPlaneSourceReveal m select) X,
      Y ∈ slitScreenPlaneJointSourceEvent m ∩ slitScreenConnectorEvent m →
      (PottsContinuity.PD.FK.configurationSplitEquiv (slitBoxGraph (16 * m))
        (slitScreenPlaneSourceReveal m select X) Y).1 ∈
        (slitScreenPlaneSourceDecoder m select X) ⁻¹'
          slitScreenPlaneSourceCapEvent m select positive X

end
end PottsContinuity.Thm4Plane
