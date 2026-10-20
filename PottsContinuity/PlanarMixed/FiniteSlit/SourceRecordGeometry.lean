module

public import PottsContinuity.PlanarMixed.FiniteSlit.SourcePaths
public import PottsContinuity.PlanarMixed.FiniteSlit.CrosscutBand
public import PottsContinuity.PlanarMixed.CutExteriorReveals

/-! Literal source geometry for a revealed carrier and its frozen open state.
The slit tip and finite truncation may vary from record to record. -/

@[expose] public section

namespace PottsContinuity.PlanarMixed.FiniteSlit
open PD.FK BD12 Exploration
noncomputable section
attribute [local instance] configurationMeasurableSpace remainingConfigurationMeasurableSpace
local instance sourceRecordGeometryEdgeDecidableEq {U : Type*} (H : SimpleGraph U) :
    DecidableEq H.edgeSet := Classical.decEq _

/-- Geometric data only: actual paths, their open bonds, the literal source
embedding, and equalities of exposed carriers and frozen states. -/
structure SourceBandGeometry {W U : Type*} [Finite W] [Finite U]
    (S : SimpleGraph W) (H : SimpleGraph U) (j : W ↪ U) (hSH : S.map j ≤ H)
    (I J : Set W) (exposed frozen : Configuration H) where
  size : ℕ
  column : ℤ
  tip : ℤ
  cuts : CrosscutData size column tip
  size_ge : 2 ≤ size
  tip_pos : 0 < tip
  tip_lt : tip < (size : ℤ)
  state : Configuration (graph size column tip)
  first_open : ∀ {u v : Vertex size column}, s(u,v) ∈ cuts.first.edges →
    (openGraph (graph size column tip) state).Adj u v
  second_open : ∀ {u v : Vertex size column}, s(u,v) ∈ cuts.second.edges →
    (openGraph (graph size column tip) state).Adj u v
  intoSource : rankedBandVertices (cuts.rank size_ge tip_pos) ↪ W
  map_le : (rankedBandGraph (graph size column tip)
    (cuts.rank size_ge tip_pos)).map intoSource ≤ S
  state_eq : embeddedConfigurationRestriction _ (graph size column tip)
    (rankedBandEmbedding (cuts.rank size_ge tip_pos)) (rankedBandGraph_map_le _ _) state =
      embeddedConfigurationRestriction _ H (intoSource.trans j)
        (composed_map_le _ S H intoSource j map_le hSH) frozen
  first_in : intoSource (cuts.firstStartBand size_ge tip_pos) ∈ I
  second_in : intoSource (cuts.secondStartBand size_ge tip_pos) ∈ J
  carrier_eq : exposed = subgraphRemovedEdges
    (SimpleGraph.map (intoSource.trans j)
      (edgeRestriction (rankedBandGraph (graph size column tip) (cuts.rank size_ge tip_pos))
        (bandArcBonds (graph size column tip) (cuts.rank size_ge tip_pos)))) H

variable {W U : Type*} [Finite W] [Finite U]
  {S : SimpleGraph W} {H : SimpleGraph U} {j : W ↪ U} {hSH : S.map j ≤ H}
  {I J : Set W}

end
end PottsContinuity.PlanarMixed.FiniteSlit
