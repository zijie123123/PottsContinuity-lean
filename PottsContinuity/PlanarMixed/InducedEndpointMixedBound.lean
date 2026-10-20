module

public import PottsContinuity.DualityExt.PositiveInducedSourceBoundaryLaw
public import PottsContinuity.PD.FK.Isomorphism
public import PottsContinuity.PD.FK.IsolatedBoundaryLaw
public import PottsContinuity.PlanarMixed.EmbeddedBoundaryLower
public import PottsContinuity.PlanarMixed.EmbeddedOpenRestriction
public import PottsContinuity.PlanarMixed.OmegaInterfaces
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import PottsContinuity.DualityExt.PositiveIsolatedBoundaryLaw
public import PottsContinuity.PlanarTopology.PolygonFourArcExistence

@[expose] public section

namespace PottsContinuity.PlanarMixed
open PD.FK PD.Duality DualityExt BD12
noncomputable section

/-- The full host dual is canonically the isolated extension of the
endpoint-only graph `DualityExt.positiveActiveGraph`. This identity needs no geometric
representation premise. -/
def inducedEndpointDualCarrierIso
    {V : Type*} [Finite V] {a : LatticeVertex} {w h : ℕ} {G : SimpleGraph V}
    (f : V ↪ RectangleVertex a w h) (hG : (G).map f ≤ rectangleGraph a w h) :
    rectangleSubgraphDualGraph hG ≃g
      (positiveActiveGraph (rectangleSubgraphDualGraph hG)).map
        (positiveActiveInclusion (rectangleSubgraphDualGraph hG)) := by
  rw [positiveActiveGraph_map_subtype]

section Endpoint
variable {V : Type*} [Finite V] {a : LatticeVertex} {w h : ℕ} (G : SimpleGraph V)
  (f : V ↪ RectangleVertex a w h) (hG : (G).map f ≤ rectangleGraph a w h)
local notation "D" => positiveActiveGraph (rectangleSubgraphDualGraph hG)
local notation "ι" => positiveActiveInclusion (rectangleSubgraphDualGraph hG)
local notation "d" => inducedEndpointDualCarrierIso f hG

end Endpoint

local instance inducedEndpointPolygonVertexFinite {m : ℕ} (P : FKC.LatticePolygon m)
    (δ : FKC.PositiveMesh) : Finite (FKC.DomainVertex δ (P.domain δ)) :=
  P.finite_domainVertex δ

section Polygon
variable {m : ℕ} (P : FKC.LatticePolygon m) (δ : FKC.PositiveMesh)
  (i j t : ℕ) (hi : 1 ≤ i) (hij : i < j) (hjt : j ≤ t) (ht : t < m+3)
  {a : LatticeVertex} {w h : ℕ}
  (f : FKC.DomainVertex δ (P.domain δ) ↪ RectangleVertex a w h)
  (hG : (FKC.domainLatticeGraph δ (P.domain δ)).map f ≤ rectangleGraph a w h)
local notation "G" => FKC.domainLatticeGraph δ (P.domain δ)
local notation "A" => P.forwardArcVertices δ 0 i
local notation "C" => (PlanarTopology.polygonBoundaryVertices P δ
  (Set.ofPred fun (z : ZMod (m+3)) => j ≤ ZMod.val z ∧ ZMod.val z ≤ t))
local notation "D" => positiveActiveGraph (rectangleSubgraphDualGraph hG)
local notation "ι" => positiveActiveInclusion (rectangleSubgraphDualGraph hG)
local notation "d" => inducedEndpointDualCarrierIso f hG

end Polygon

end
end PottsContinuity.PlanarMixed
