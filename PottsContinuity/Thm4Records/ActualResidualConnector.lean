module

public import PottsContinuity.Thm4Records.ResidualCarrier
public import PottsContinuity.PlanarMixed.Lemma4RecordCarrier.ActualNativePrimalLaw

@[expose] public section

namespace PottsContinuity.Thm4Records
open PD.FK Exploration Push RSW Thm4Plane
noncomputable section

/-- Every queried original bond is absent from this carrier, in either state. -/
abbrev connectorNativeGraph (m : ℕ) (hm : 1 ≤ m)
    (X : Configuration (FKC.FiniteFK.slitBoxGraph (16*m))) :=
  edgeRestriction (FKC.FiniteFK.slitBoxGraph (16*m)) (connectorReveal m hm X)

/-- The native primal state retains only unqueried original bonds. -/
def connectorNativeRead (m : ℕ) (hm : 1 ≤ m)
    (X Y : Configuration (FKC.FiniteFK.slitBoxGraph (16*m))) :
    Configuration (connectorNativeGraph m hm X) :=
  PlanarMixed.Lemma4Connectors.nativeUnqueriedRead _ (connectorReveal m hm X) Y

/-- Restore deleted bonds as dual-open, independently of their recorded states. -/
def connectorAuxiliaryDual (m : ℕ) (hm : 1 ≤ m)
    (R : Configuration (FKC.FiniteFK.slitBoxGraph (16*m)))
    (U : RemainingConfiguration (FKC.FiniteFK.slitBoxGraph (16*m)) R) :
    Configuration (SlitRStarGraph m) := slitRStarDualConfiguration m hm U.val

@[simp] theorem mem_connectorAuxiliaryDual (m : ℕ) (hm : 1 ≤ m)
    (R : Configuration (FKC.FiniteFK.slitBoxGraph (16*m)))
    (U : RemainingConfiguration (FKC.FiniteFK.slitBoxGraph (16*m)) R)
    (e : (SlitRStarGraph m).edgeSet) :
    e ∈ connectorAuxiliaryDual m hm R U ↔
      (slitRStarEdgeBridge m hm e).primalEdge ∉ U.val :=
  mem_slitRStarDualConfiguration m hm U.val e

/-- A dual connection across the entire square in the auxiliary state. -/
def connectorAuxiliaryCrossing (m : ℕ) (hm : 1 ≤ m)
    (R : Configuration (FKC.FiniteFK.slitBoxGraph (16*m))) :
    Set (RemainingConfiguration (FKC.FiniteFK.slitBoxGraph (16*m)) R) :=
  {U | ∃ u v : SlitRStarVertex m,
    u.val.1 = -(5*(m:ℤ)) ∧ v.val.1 = 5*(m:ℤ)-1 ∧
      ActualConnected (SlitRStarGraph m) (connectorAuxiliaryDual m hm R U) u v}

/-- The corrected auxiliary state is a read of the native configuration alone. -/
def connectorNativeAuxiliaryDual (m : ℕ) (hm : 1 ≤ m)
    (X : Configuration (FKC.FiniteFK.slitBoxGraph (16*m)))
    (C : Configuration (connectorNativeGraph m hm X)) :
    Configuration (SlitRStarGraph m) :=
  connectorAuxiliaryDual m hm (connectorReveal m hm X)
    (edgeRestrictionConfigurationEquiv _ (connectorReveal m hm X) C)

@[simp] theorem connectorNativeAuxiliaryDual_read (m : ℕ) (hm : 1 ≤ m)
    (X Y : Configuration (FKC.FiniteFK.slitBoxGraph (16*m))) :
    connectorNativeAuxiliaryDual m hm X (connectorNativeRead m hm X Y) =
      slitRStarDualConfiguration m hm Y ∪
        recordedDualEdges m hm (connectorReveal m hm X) := by
  unfold connectorNativeAuxiliaryDual connectorNativeRead
  rw [PlanarMixed.Lemma4Connectors.nativeUnqueriedRead,Equiv.apply_symm_apply]
  classical
  ext e
  rw [mem_connectorAuxiliaryDual,Finset.mem_union,mem_slitRStarDualConfiguration,
    mem_recordedDualEdges]
  simp only [configurationSplitEquiv,Equiv.coe_fn_mk,Finset.mem_sdiff]
  tauto

end
end PottsContinuity.Thm4Records
