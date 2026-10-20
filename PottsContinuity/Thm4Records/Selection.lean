module

public import PottsContinuity.Thm4Records.ClusterFrontier
public import PottsContinuity.FKC.FiniteFK.SlitScreenCrossingEvents

@[expose] public section

namespace PottsContinuity.Thm4Records
open PD.FK Exploration Push RSW Thm4Plane
noncomputable section

/-- The inner vertical side opposite the seed side of a censored window. -/
def sideInnerVertices (m : ℕ) (right : Bool) :
    Set (FKC.FiniteFK.SlitBoxVertex (16*m)) :=
  {v | v.val.1 = if right then (m:ℤ) else -(m:ℤ)}

/-- Actual censored primal connection from the outer to the inner side. -/
def sidePrimalConnectionEvent (m : ℕ) (right : Bool) :
    Set (Configuration (FKC.FiniteFK.slitBoxGraph (16*m))) :=
  {A | ∃ v ∈ sideInnerVertices m right,
    v ∈ Thm3.Prop4.censoredSeedCluster
      (sideCensoredGraph_le m right) (sideOuterSeeds m right) A}

/-- The deterministic primal/dual complement statement on the fixed original source
carriers: the side screen crossing occurs iff the side primal connection fails. -/
def SidePrimalDualAlternative (m : ℕ) (right : Bool) : Prop :=
  ∀ A : Configuration (FKC.FiniteFK.slitBoxGraph (16*m)),
    A ∈ (if right then FKC.FiniteFK.slitScreenRightCrossingEvent m
      else FKC.FiniteFK.slitScreenLeftCrossingEvent m) ↔
    A ∉ sidePrimalConnectionEvent m right

theorem sidePrimalConnectionEvent_readFrom_connectorReveal
    (m : ℕ) (hm : 1 ≤ m) (right : Bool) :
    ReadFromReveal (connectorReveal m hm) (sidePrimalConnectionEvent m right) :=
  sideSeedConnection_readFrom_connectorReveal m hm right (sideInnerVertices m right)

/-- Only the fixed-window deterministic primal/dual alternative remains in
this record-readability adapter. No probability or boundary law is presumed. -/
theorem sideCrossing_readFrom_connectorReveal_of_primalDualAlternative
    (m : ℕ) (hm : 1 ≤ m) (right : Bool)
    (hAlt : SidePrimalDualAlternative m right) :
    ReadFromReveal (connectorReveal m hm)
      (if right then FKC.FiniteFK.slitScreenRightCrossingEvent m
        else FKC.FiniteFK.slitScreenLeftCrossingEvent m) := by
  intro A B hB
  rw [hAlt B,hAlt A]
  exact not_congr (sidePrimalConnectionEvent_readFrom_connectorReveal m hm right A B hB)

/-- The actual source joint event: the slit screen event together with the left and right
screen crossings. -/
def connectorSourceEvent (m : ℕ) :
    Set (Configuration (FKC.FiniteFK.slitBoxGraph (16*m))) :=
  slitScreenEvent m ∩ (FKC.FiniteFK.slitScreenLeftCrossingEvent m ∩
    FKC.FiniteFK.slitScreenRightCrossingEvent m)

/-- Select attained observations of exactly the source joint event. -/
def connectorSelectedObservations (m : ℕ) (hm : 1 ≤ m) :
    Set (StoppingObservationRange (connectorReveal m hm)) :=
  selectedRevealObservations (connectorReveal m hm) (connectorSourceEvent m)

theorem connectorSourceEvent_readFrom_connectorReveal_of_primalDualAlternatives
    (m : ℕ) (hm : 1 ≤ m)
    (hLeft : SidePrimalDualAlternative m false)
    (hRight : SidePrimalDualAlternative m true) :
    ReadFromReveal (connectorReveal m hm) (connectorSourceEvent m) := by
  intro A B hB
  exact and_congr (screenEvent_readFrom_connectorReveal m hm A B hB)
    (and_congr
      (sideCrossing_readFrom_connectorReveal_of_primalDualAlternative m hm false hLeft A B hB)
      (sideCrossing_readFrom_connectorReveal_of_primalDualAlternative m hm true hRight A B hB))

theorem connectorSelectedObservations_preimage_of_primalDualAlternatives
    (m : ℕ) (hm : 1 ≤ m)
    (hLeft : SidePrimalDualAlternative m false)
    (hRight : SidePrimalDualAlternative m true) :
    stoppingObservationMap (connectorReveal m hm) ⁻¹' connectorSelectedObservations m hm =
      connectorSourceEvent m :=
  preimage_selectedRevealObservations _ _
    (connectorSourceEvent_readFrom_connectorReveal_of_primalDualAlternatives m hm hLeft hRight)

end
end PottsContinuity.Thm4Records
