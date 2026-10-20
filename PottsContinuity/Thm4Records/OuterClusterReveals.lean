module

public import PottsContinuity.Thm3.Prop4.CensoredClusterReveal
public import PottsContinuity.Thm3.Push.CommonExplorationEvents
public import PottsContinuity.Thm4Plane.ScreenDominatedBallReveal

@[expose] public section

namespace PottsContinuity.Thm4Records
open PD.FK Exploration Push RSW
noncomputable section

local instance connectorSourceEdgeEq (m : ℕ) :
    DecidableEq (FKC.FiniteFK.slitBoxGraph (16*m)).edgeSet := Classical.decEq _

/-- Original primal vertices of the right or left side-screen window. -/
def sideWindow (m : ℕ) (right : Bool) : Set (FKC.FiniteFK.SlitBoxVertex (16*m)) :=
  {v | if right then (m:ℤ) ≤ v.val.1 ∧ v.val.1 ≤ 5*(m:ℤ)
    else -(5*(m:ℤ)) ≤ v.val.1 ∧ v.val.1 ≤ -(m:ℤ)}

/-- The actual source graph censored to the chosen closed side window. -/
def sideCensoredGraph (m : ℕ) (right : Bool) :
    SimpleGraph (FKC.FiniteFK.SlitBoxVertex (16*m)) where
  Adj u v := (FKC.FiniteFK.slitBoxGraph (16*m)).Adj u v ∧
    u ∈ sideWindow m right ∧ v ∈ sideWindow m right
  symm := ⟨by intro u v h; exact ⟨h.1.symm,h.2.2,h.2.1⟩⟩
  loopless := ⟨by intro u h; exact (FKC.FiniteFK.slitBoxGraph (16*m)).loopless.irrefl u h.1⟩

theorem sideCensoredGraph_le (m : ℕ) (right : Bool) :
    sideCensoredGraph m right ≤ FKC.FiniteFK.slitBoxGraph (16*m) :=
  fun _ _ h => h.1

/-- All vertices on the original outer vertical side seed the exploration. -/
def sideOuterSeeds (m : ℕ) (right : Bool) : Set (FKC.FiniteFK.SlitBoxVertex (16*m)) :=
  {v | v.val.1 = if right then 5*(m:ℤ) else -(5*(m:ℤ))}

/-- The complete source-edge record of the censored outer-side clusters. -/
def sideOuterClusterReveal (m : ℕ) (right : Bool) :
    RevealMap (G := FKC.FiniteFK.slitBoxGraph (16*m)) :=
  Thm3.Prop4.censoredSeedReveal (sideCensoredGraph_le m right) (sideOuterSeeds m right)

theorem sideOuterClusterReveal_stable (m : ℕ) (right : Bool)
    (A B : Configuration (FKC.FiniteFK.slitBoxGraph (16*m)))
    (h : B ∩ sideOuterClusterReveal m right A = A ∩ sideOuterClusterReveal m right A) :
    sideOuterClusterReveal m right B = sideOuterClusterReveal m right A :=
  Thm3.Prop4.censoredSeedReveal_stable (sideCensoredGraph_le m right) (sideOuterSeeds m right) A B h

/-- Both outer-side records are kept in one stopping observation. -/
def sideJointReveal (m : ℕ) : RevealMap (G := FKC.FiniteFK.slitBoxGraph (16*m)) :=
  jointReveal (sideOuterClusterReveal m false) (sideOuterClusterReveal m true)

theorem sideJointReveal_stable (m : ℕ) :
    ∀ A B, B ∩ sideJointReveal m A = A ∩ sideJointReveal m A →
      sideJointReveal m B = sideJointReveal m A :=
  jointReveal_stable _ _ (sideOuterClusterReveal_stable m false) (sideOuterClusterReveal_stable m true)

/-- The initial common source record includes the local screen observation. -/
def connectorClusterReveal (m : ℕ) : RevealMap (G := FKC.FiniteFK.slitBoxGraph (16*m)) :=
  jointReveal (Thm4Plane.slitScreenBallReveal m) (sideJointReveal m)

theorem connectorClusterReveal_stable (m : ℕ) :
    ∀ A B, B ∩ connectorClusterReveal m A = A ∩ connectorClusterReveal m A →
      connectorClusterReveal m B = connectorClusterReveal m A :=
  jointReveal_stable _ _ (by intro A B _; rfl) (sideJointReveal_stable m)

/-- E is already readable on this concrete common record. -/
theorem screenEvent_readFrom_connectorClusterReveal (m : ℕ) :
    ReadFromReveal (connectorClusterReveal m) (Thm4Plane.slitScreenEvent m) := by
  apply readFromReveal_joint_left _ _ (by intro A B _; rfl) (sideJointReveal_stable m)
  intro A B hB
  apply Thm4Plane.slitScreenEvent_iff_of_agree_ballReveal m B A
  exact hB.2

end
end PottsContinuity.Thm4Records
