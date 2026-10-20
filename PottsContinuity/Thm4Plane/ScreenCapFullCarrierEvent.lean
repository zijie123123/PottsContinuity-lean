module

public import PottsContinuity.Thm4Plane.ScreenCapComplementFreeLaw
public import PottsContinuity.Thm4Plane.ScreenCapDomainPlaneEvent
public import PottsContinuity.Thm4Plane.PlaneTranslation
public import PottsContinuity.Foundations.BoxBoundary

@[expose] public section

namespace PottsContinuity.Thm4Plane

open PottsContinuity.PD.FK
open PottsContinuity.FKC.FiniteFK
open PottsContinuity.Infinite

noncomputable section

local instance screenCapFullCarrierEdgeFintype (m : ℕ)
    (R : PottsContinuity.FKC.FiniteFK.Configuration (slitBoxGraph (16 * m)))
    (D : Set (SlitBoxVertex (16 * m))) :
    Fintype (screenCapEdgeDeletedFullCarrierGraph m R D).edgeSet :=
  Fintype.ofFinite _
local instance screenCapFullCarrierSlitBoxEdgeDecidableEq (m : ℕ) :
    DecidableEq (slitBoxGraph (16 * m)).edgeSet := Classical.decEq _

/-- The full-carrier version of the cap connection event. The selected graph
has the fixed slit-box vertex type and retains only the edges inside the
edge-deleted cap component. -/
def screenCapFullCarrierBoundaryConnectionEvent (m : ℕ)
    (R : PottsContinuity.FKC.FiniteFK.Configuration (slitBoxGraph (16 * m)))
    (D : Set (SlitBoxVertex (16 * m)))
    (hcap : screenTargetCap m ⊆ D) :
    Set (PottsContinuity.FKC.FiniteFK.Configuration (screenCapEdgeDeletedFullCarrierGraph m R D)) :=
  {C | ∃ v : {x : SlitBoxVertex (16 * m) // x ∈ D},
    v.val ∈ screenTargetCap m ∧
      (|v.val.val.1| = (m : ℤ) ∨ v.val.val.2 = -(15 * (m : ℤ))) ∧
      PottsContinuity.PD.FK.ActualConnected
        (screenCapEdgeDeletedFullCarrierGraph m R D) C
        (screenCapDomainVertexEmbeddingToSlitBox m D
          ⟨slitBoxBottomCenterVertex (16 * m),
            hcap (screenTargetCap_bottomCenter_mem m)⟩)
        (screenCapDomainVertexEmbeddingToSlitBox m D v)}

/-- Decode a complement record remainder directly to the fixed full cap
carrier. -/
def screenCapComplementRevealFullCarrierDecoder (m : ℕ)
    (R : PottsContinuity.FKC.FiniteFK.Configuration (slitBoxGraph (16 * m)))
    (D : Set (SlitBoxVertex (16 * m)))
    (X : PottsContinuity.FKC.FiniteFK.Configuration (slitBoxGraph (16 * m))) :
    PottsContinuity.PD.FK.RemainingConfiguration
      (slitBoxGraph (16 * m)) (screenCapComplementReveal m R D X) →
      PottsContinuity.FKC.FiniteFK.Configuration
        (screenCapEdgeDeletedFullCarrierGraph m R D) := by
  change PottsContinuity.PD.FK.RemainingConfiguration
      (slitBoxGraph (16 * m))
      (PottsContinuity.PD.FK.subgraphRemovedEdges
        (screenCapEdgeDeletedFullCarrierGraph m R D) (slitBoxGraph (16 * m))) →
      PottsContinuity.PD.FK.Configuration
        (screenCapEdgeDeletedFullCarrierGraph m R D)
  exact fun C => (PottsContinuity.PD.FK.subgraphRemainingConfigurationEquiv
    (screenCapEdgeDeletedFullCarrierGraph_le_slitBox m R D)).symm C

end
end PottsContinuity.Thm4Plane
