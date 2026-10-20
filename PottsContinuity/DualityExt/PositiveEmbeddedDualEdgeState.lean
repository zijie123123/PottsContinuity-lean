module

public import PottsContinuity.DualityExt.PositiveDualSubgraphEdgeState
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Maps

@[expose] public section

namespace PottsContinuity.DualityExt

open PottsContinuity.PD.FK

noncomputable section

/-- The retained dual edge of an embedded source edge is open exactly when
the source edge is closed. -/
theorem embeddedRectangleSubgraphDualConfiguration_edgeState
    {V W : Type*} [Finite V] [Finite W]
    {G : SimpleGraph V} {a : PD.FK.LatticeVertex} {w h : ℕ}
    (f : V ↪ RectangleVertex a w h)
    (hG : G.map f ≤ rectangleGraph a w h)
    (C : Configuration G) (g : G.edgeSet) :
    rectangleSubgraphDualEdgeEmbedding hG
        (isolatedExtensionEdgeEquiv G f g) ∈
      rectangleSubgraphDualConfigurationEquiv hG
        (isolatedExtensionConfigurationEquiv G f C) ↔
      g ∉ C := by
  rw [rectangleSubgraphDualConfigurationEquiv_edgeState]
  have hmem : (isolatedExtensionEdgeEquiv G f g) ∈
      isolatedExtensionConfigurationEquiv G f C ↔ g ∈ C := by
    simp [isolatedExtensionConfigurationEquiv]
  exact not_congr hmem

end

end PottsContinuity.DualityExt
