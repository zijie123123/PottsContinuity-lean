module

public import PottsContinuity.DualityExt.PositiveConditionedSubgraphDuality
public import PottsContinuity.DualityExt.PositivePDLawBridge
public import PottsContinuity.DualityExt.PositiveIsolatedBoundaryLaw
public import PottsContinuity.DualityExt.PositiveSubgraphDualEdgeEquiv
public import PottsContinuity.PD.FK.RemainingComparison
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import PottsContinuity.Thm4Side.RevealConditionedHost
public import PottsContinuity.Thm4Side.DualRectangleReveal
public import PottsContinuity.Thm4Side.ResidualHalfEdges
public import PottsContinuity.FKC.Medial.WholePlaneDualConfiguration
public import PottsContinuity.Thm4Plane.ScreenSideFactor

@[expose] public section

namespace PottsContinuity.Thm4Side

open PottsContinuity.DualityExt
open PottsContinuity.Exploration
open PottsContinuity.FKC.FiniteFK
open PottsContinuity.PD.FK
open PottsContinuity.RSW
open PottsContinuity.Thm4
open PottsContinuity.Thm4Plane

noncomputable section

/-- Vertices of the one-size-larger rectangle host used by the conditioned
dual law. -/
abbrev sideExactLawHostVertex (n : ℕ) :=
  RectangleVertex (-((n + 1 : ℕ) : ℤ), -((n + 1 : ℕ) : ℤ))
    (2 * (n + 1)) (2 * (n + 1))

/-- The one-size-larger rectangle graph carrying the auxiliary open ring. -/
abbrev sideExactLawHostGraph (n : ℕ) :=
  rectangleGraph (-((n + 1 : ℕ) : ℤ), -((n + 1 : ℕ) : ℤ))
    (2 * (n + 1)) (2 * (n + 1))

/-- The full fixed-reveal residual edge graph before taking its active graph. -/
abbrev sideExactLawResidual (m : ℕ)
    (R : PD.FK.Configuration (slitBoxGraph (16 * m))) :=
  PD.FK.edgeRestriction (slitBoxGraph (16 * m)) R

/-- Embed the active residual graph into the auxiliary-ring host. -/
noncomputable def sideExactLawHostEmbedding (m : ℕ)
    (R : PD.FK.Configuration (slitBoxGraph (16 * m))) :
    positiveActiveVertexSet (sideExactLawResidual m R) ↪
      sideExactLawHostVertex (16 * m) :=
  (positiveActiveInclusion (sideExactLawResidual m R)).trans
    (slitBoxAuxiliaryHostEmbedding (16 * m))

/-- The embedded active residual graph is a host subgraph. -/
theorem sideExactLawHostSubgraph_le (m : ℕ)
    (R : PD.FK.Configuration (slitBoxGraph (16 * m))) :
    (positiveActiveGraph (sideExactLawResidual m R)).map
        (sideExactLawHostEmbedding m R) ≤ sideExactLawHostGraph (16 * m) := by
  let J := sideExactLawResidual m R
  let i := positiveActiveInclusion J
  let f := slitBoxAuxiliaryHostEmbedding (16 * m)
  have hactive : (positiveActiveGraph J).map i = J :=
    positiveActiveGraph_map_subtype J
  have hmap : (positiveActiveGraph J).map (sideExactLawHostEmbedding m R) =
      J.map f := by
    change (positiveActiveGraph J).map (f ∘ i) = J.map f
    rw [← SimpleGraph.map_map, hactive]
  have hsub : J.map f ≤ (slitBoxGraph (16 * m)).map f := by
    intro u v huv
    rw [SimpleGraph.map_adj] at huv ⊢
    rcases huv with ⟨u₀, v₀, hadj, rfl, rfl⟩
    exact ⟨u₀, v₀, PD.FK.edgeRestriction_le (slitBoxGraph (16 * m)) R hadj,
      rfl, rfl⟩
  rw [hmap]
  exact le_trans hsub (slitBoxAuxiliaryHostEmbedding_graph_le (16 * m))

end
end PottsContinuity.Thm4Side
