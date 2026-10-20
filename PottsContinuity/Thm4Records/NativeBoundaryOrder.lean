module

public import PottsContinuity.Thm4Records.ActualResidualConnector
public import PottsContinuity.PlanarMixed.Lemma4RecordCarrier.IncidentVertexLaw
public import PottsContinuity.PlanarMixed.Lemma4RecordCarrier.DecreasingEmbeddedComparison

@[expose] public section

namespace PottsContinuity.Thm4Records
open PD.FK Exploration Push RSW Thm4Plane
open PlanarMixed.Lemma4Connectors
noncomputable section

/-- Frozen open edges and pre-existing boundary identifications can attach to
native vertices only on the prescribed wiring set. -/
theorem frozen_partition_le_wired_of_endpoint_attachment
    {V W : Type*} (H : SimpleGraph W) (f : V ↪ W) (B : Set V)
    (ξ : BoundaryCondition W) (K : Configuration H)
    (hattach : ∀ e ∈ K, ∀ v, f v ∈ e.val → v ∈ B)
    (hboundary : ∀ v, f v ∈ ξ.boundary → v ∈ B) :
    (isolatedExtensionPullbackBoundary f (frozenBoundary ξ K)).partition ≤
      (BoundaryCondition.wired B).partition := by
  let D : Set W := {w | ∀ v, f v=w → v ∈ B}
  have hbound : (frozenBoundary ξ K).partition ≤ (BoundaryCondition.wired D).partition := by
    apply componentSetoid_le
    · apply reachableSetoid_le_of_adj
      intro x y hxy
      obtain ⟨e,he,heq⟩ := (openGraph_adj H K x y).mp hxy
      apply (BoundaryCondition.wired_rel D x y).mpr
      right
      constructor
      · intro v hv
        exact hattach e he v (by rw [hv,heq]; exact Sym2.mem_mk_left _ _)
      · intro v hv
        exact hattach e he v (by rw [hv,heq]; exact Sym2.mem_mk_right _ _)
    · intro x y hxy
      apply (BoundaryCondition.wired_rel D x y).mpr
      rcases ξ.supported hxy with rfl | ⟨hx,hy⟩
      · exact Or.inl rfl
      · exact Or.inr ⟨fun v hv => hboundary v (hv ▸ hx),
          fun v hv => hboundary v (hv ▸ hy)⟩
  intro u v huv
  rcases (BoundaryCondition.wired_rel D (f u) (f v)).mp (hbound huv) with h | ⟨hu,hv⟩
  · exact Or.inl (f.injective h)
  · exact Or.inr ⟨hu u rfl,hv v rfl⟩

abbrev connectorNativeVertex (m : ℕ) (hm : 1 ≤ m)
    (X : Configuration (FKC.FiniteFK.slitBoxGraph (16*m))) :=
  incidentVertexSet (connectorNativeGraph m hm X)

abbrev connectorIncidentGraph (m : ℕ) (hm : 1 ≤ m)
    (X : Configuration (FKC.FiniteFK.slitBoxGraph (16*m))) :=
  (connectorNativeGraph m hm X).induce (connectorNativeVertex m hm X)

/-- The two primal terminal rows of the square's actual residual carrier. -/
def connectorNativeTopBottom (m : ℕ) (hm : 1 ≤ m)
    (X : Configuration (FKC.FiniteFK.slitBoxGraph (16*m))) :
    Set (connectorNativeVertex m hm X) :=
  {u | u.val.val.2 = -(12*(m:ℤ)) ∨ u.val.val.2 = -(2*(m:ℤ))}

/-- The literal induced boundary after removal of vertices carrying no bonds. -/
def connectorIncidentBoundary (m : ℕ) (hm : 1 ≤ m)
    (X : Configuration (FKC.FiniteFK.slitBoxGraph (16*m)))
    (ξ : BoundaryCondition (FKC.FiniteFK.SlitBoxVertex (16*m))) :=
  isolatedExtensionPullbackBoundary (incidentVertexEmbedding (connectorNativeGraph m hm X))
    (frozenBoundary ξ (revealRecordConfiguration (connectorReveal m hm) X).val)

/-- No probability law or boundary order is assumed: the geometric endpoint
conditions imply the required order for the actual induced partition. -/
theorem connectorIncidentBoundary_le_topBottom_of_endpoint_attachment
    (m : ℕ) (hm : 1 ≤ m)
    (X : Configuration (FKC.FiniteFK.slitBoxGraph (16*m)))
    (ξ : BoundaryCondition (FKC.FiniteFK.SlitBoxVertex (16*m)))
    (hattach : ∀ e ∈ (revealRecordConfiguration (connectorReveal m hm) X).val,
      ∀ u : connectorNativeVertex m hm X, u.val ∈ e.val → u ∈ connectorNativeTopBottom m hm X)
    (hboundary : ∀ u : connectorNativeVertex m hm X,
      u.val ∈ ξ.boundary → u ∈ connectorNativeTopBottom m hm X) :
    (connectorIncidentBoundary m hm X ξ).partition ≤
      (BoundaryCondition.wired (connectorNativeTopBottom m hm X)).partition :=
  frozen_partition_le_wired_of_endpoint_attachment _ _ _ ξ _ hattach hboundary

/-- The stopped native law loses only isolated vertices under this exact read. -/
theorem connectorIncidentGraph_law (m : ℕ) (hm : 1 ≤ m)
    (X : Configuration (FKC.FiniteFK.slitBoxGraph (16*m)))
    (θ : Parameters) (ξ : BoundaryCondition (FKC.FiniteFK.SlitBoxVertex (16*m))) :
    (law (connectorNativeGraph m hm X) θ
      (frozenBoundary ξ (revealRecordConfiguration (connectorReveal m hm) X).val)).map
        (incidentVertexConfigurationRead (connectorNativeGraph m hm X)) =
      law (connectorIncidentGraph m hm X) θ (connectorIncidentBoundary m hm X ξ) :=
  incidentVertexConfigurationRead_law _ θ _

end
end PottsContinuity.Thm4Records
