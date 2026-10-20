module

public import PottsContinuity.DualityExt.PositivePDLawBridge
public import PottsContinuity.DualityExt.PositiveBoundaryMergeDualTransfer
public import PottsContinuity.PD.FK.IncreasingEvents
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# Wired-side duality with the boundary partition induced by rectangle restriction

When a dual subgraph is embedded in a rectangular host, the complementary
primal boundary relation is defined by host exterior wiring and the duals of
the deleted host bonds. The law theorem below names that full partition rather
than requiring a separate equality premise for a target boundary condition.
-/

@[expose] public section

namespace PottsContinuity.DualityExt

open PottsContinuity.PD.FK
open PottsContinuity.PD.Duality

noncomputable section

variable {a : LatticeVertex} {w h : ℕ}
variable {K : SimpleGraph (RectangleVertex a w h)}

local instance inducedWiredConfigFintype {V : Type*} [Finite V]
    {G : SimpleGraph V} : Fintype (Configuration G) := Fintype.ofFinite _
local instance inducedWiredConfigDecidableEq {V : Type*} [Finite V]
    {G : SimpleGraph V} : DecidableEq (Configuration G) := Classical.decEq _

/-- Boundary partition on the endpoint carrier of the double dual, induced
by the rectangular host exterior wiring and by forced-open duals of deleted
edges. For a graph with holes this may have several classes. -/
def positiveWiredSubgraphDualBoundary
    (hK : K ≤ rectangleGraph a w h)
    {W : Type*} [Finite W]
    (e : positiveActiveVertexSet (rectangleSubgraphDualGraph hK) ≃ W) :
    BoundaryCondition W :=
  positiveBoundaryTransport e
    (isolatedExtensionPullbackBoundary
      (positiveActiveInclusion (rectangleSubgraphDualGraph hK))
      (frozenBoundary (rectangleDualBoundaryCondition a w h)
        (rectangleSubgraphRemovedDualEdges hK)))

/-- Configuration equivalence from the active double-dual graph to the
rectangular dual subgraph. -/
def positiveWiredSubgraphDualConfigurationEquiv
    (hK : K ≤ rectangleGraph a w h)
    {W : Type*} [Finite W]
    (e : positiveActiveVertexSet (rectangleSubgraphDualGraph hK) ≃ W) :
    Configuration ((positiveActiveGraph (rectangleSubgraphDualGraph hK)).map
      e.toEmbedding) ≃ Configuration K :=
  (((rectangleSubgraphDualConfigurationEquiv hK).trans
      (positiveActiveConfigurationEquiv (rectangleSubgraphDualGraph hK)).symm).trans
      (isolatedExtensionConfigurationEquiv
        (positiveActiveGraph (rectangleSubgraphDualGraph hK)) e.toEmbedding)).symm

/-- The wired-side dual law for a rectangular edge subgraph, with its exact
induced case-by-case boundary partition. This is the reverse form of the
free-subgraph law and is valid whether or not the source graph is simply
connected. -/
theorem positive_wired_subgraph_duality_law_induced_boundary
    (hK : K ≤ rectangleGraph a w h)
    {q p : ℝ} (hq : 0 < q) (hp : 0 < p) (hp1 : p < 1)
    {W : Type*} [Finite W]
    (e : positiveActiveVertexSet (rectangleSubgraphDualGraph hK) ≃ W) :
    (positiveFKLaw
        ((positiveActiveGraph (rectangleSubgraphDualGraph hK)).map e.toEmbedding)
        q p hq hp hp1 (positiveWiredSubgraphDualBoundary hK e)).map
      (positiveWiredSubgraphDualConfigurationEquiv hK e) =
      positiveFKLaw K q (dualParameter q p) hq
        (dualParameter_pos hq hp hp1) (dualParameter_lt_one hq hp hp1)
        (BoundaryCondition.free ∅) := by
  simpa only [positiveWiredSubgraphDualBoundary,
    positiveWiredSubgraphDualConfigurationEquiv] using
    positive_wired_dual_subgraph_law_of_partition_eq hK hq hp hp1 e
      (positiveWiredSubgraphDualBoundary hK e) rfl

end
end PottsContinuity.DualityExt
