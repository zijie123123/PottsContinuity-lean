module

public import PottsContinuity.DualityExt.PositiveAnnulusPrimalPartition
public import PottsContinuity.DualityExt.PositiveDomainMarkov
public import PottsContinuity.DualityExt.PositiveIsolatedBoundaryLaw
public import PottsContinuity.DualityExt.PositiveInducedWiredDuality
public import PottsContinuity.DualityExt.PositivePDLawBridge
public import PottsContinuity.DualityExt.PositiveTwoBlockPullback
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.Probability.ProbabilityMassFunction.Constructions

@[expose] public section

namespace PottsContinuity.DualityExt

open PottsContinuity.PD.FK

noncomputable section

local instance annulusPrimalDMPHostEdgeFintype (N : ℕ) :
    Fintype (rectangleGraph (annulusHostAnchor N) (4 * N) (4 * N)).edgeSet :=
  Fintype.ofFinite _

local instance annulusPrimalDMPHostEdgeDecidableEq (N : ℕ) :
    DecidableEq (rectangleGraph (annulusHostAnchor N) (4 * N) (4 * N)).edgeSet :=
  Classical.decEq _

local instance annulusPrimalDMPHostConfigFintype (N : ℕ) :
    Fintype (Configuration (rectangleGraph (annulusHostAnchor N) (4 * N) (4 * N))) :=
  Fintype.ofFinite _

local instance annulusPrimalDMPHostConfigDecidableEq (N : ℕ) :
    DecidableEq (Configuration (rectangleGraph (annulusHostAnchor N) (4 * N) (4 * N))) :=
  Classical.decEq _

local instance annulusPrimalDMPRemovedFintype (N : ℕ)
    (R : Configuration (rectangleGraph (annulusHostAnchor N) (4 * N) (4 * N))) :
    Fintype (RemovedConfiguration
      (rectangleGraph (annulusHostAnchor N) (4 * N) (4 * N)) R) :=
  Fintype.ofFinite _

local instance annulusPrimalDMPRemovedDecidableEq (N : ℕ)
    (R : Configuration (rectangleGraph (annulusHostAnchor N) (4 * N) (4 * N))) :
    DecidableEq (RemovedConfiguration
      (rectangleGraph (annulusHostAnchor N) (4 * N) (4 * N)) R) :=
  Classical.decEq _

local instance annulusPrimalDMPRemainingFintype (N : ℕ)
    (R : Configuration (rectangleGraph (annulusHostAnchor N) (4 * N) (4 * N))) :
    Fintype (RemainingConfiguration
      (rectangleGraph (annulusHostAnchor N) (4 * N) (4 * N)) R) :=
  Fintype.ofFinite _

local instance annulusPrimalDMPRemainingDecidableEq (N : ℕ)
    (R : Configuration (rectangleGraph (annulusHostAnchor N) (4 * N) (4 * N))) :
    DecidableEq (RemainingConfiguration
      (rectangleGraph (annulusHostAnchor N) (4 * N) (4 * N)) R) :=
  Classical.decEq _

/-- The separately wired annulus boundary obtained by pulling back the host
inner and outer classes to the annulus carrier. -/
def annulusPrimalSeparatedBoundary (N : ℕ) (hN : 1 ≤ N) :
    BoundaryCondition {v : LatticeVertex // v ∈ annulusVertexSet N} :=
  isolatedExtensionPullbackBoundary (annulusSourceEmbedding N)
    (positiveTwoBlockBoundary (annulusHostPrimalInnerClass N)
      (annulusHostPrimalOuterClass N)
      (annulusHostPrimalInnerOuter_disjoint N hN))

/-- The inner class on the annulus carrier, obtained from the host class by
preimage under the carrier embedding. -/
def annulusPrimalInnerBoundaryClass (N : ℕ) (_hN : 1 ≤ N) :
    Set {v : LatticeVertex // v ∈ annulusVertexSet N} :=
  (annulusSourceEmbedding N) ⁻¹' annulusHostPrimalInnerClass N

/-- The outer class on the annulus carrier, obtained from the host class by
preimage under the carrier embedding. -/
def annulusPrimalOuterBoundaryClass (N : ℕ) (_hN : 1 ≤ N) :
    Set {v : LatticeVertex // v ∈ annulusVertexSet N} :=
  (annulusSourceEmbedding N) ⁻¹' annulusHostPrimalOuterClass N

/-- The inner and outer source classes are disjoint because their host
classes are disjoint. -/
theorem annulusPrimalInnerOuter_disjoint (N : ℕ) (hN : 1 ≤ N) :
    Disjoint (annulusPrimalInnerBoundaryClass N hN)
      (annulusPrimalOuterBoundaryClass N hN) := by
  rw [Set.disjoint_left]
  intro x hxI hxO
  exact (Set.disjoint_left.mp
    (annulusHostPrimalInnerOuter_disjoint N hN)) hxI hxO

/-- The separately wired source boundary partition is precisely the
two-class partition on the preimages of the host inner and outer classes. -/
theorem annulusPrimalSeparatedBoundary_partition_eq_twoBlock
    (N : ℕ) (hN : 1 ≤ N) :
    (annulusPrimalSeparatedBoundary N hN).partition =
      (positiveTwoBlockBoundary
        (annulusPrimalInnerBoundaryClass N hN)
        (annulusPrimalOuterBoundaryClass N hN)
        (annulusPrimalInnerOuter_disjoint N hN)).partition := by
  change (isolatedExtensionPullbackBoundary (annulusSourceEmbedding N)
      (positiveTwoBlockBoundary (annulusHostPrimalInnerClass N)
        (annulusHostPrimalOuterClass N)
        (annulusHostPrimalInnerOuter_disjoint N hN))).partition = _
  exact isolatedExtensionPullback_positiveTwoBlockBoundary_partition
    (annulusSourceEmbedding N) (annulusHostPrimalInnerClass N)
    (annulusHostPrimalOuterClass N)
    (annulusHostPrimalInnerOuter_disjoint N hN)

/-- The double-dual configuration map, transported through the exact graph
identification of the active double-dual carrier with the source annulus. -/
noncomputable def annulusPrimalToEmbeddedDualConfigurationEquiv
    (N : ℕ) {a : LatticeVertex} {w h : ℕ}
    {K : SimpleGraph (RectangleVertex a w h)}
    (hK : K ≤ rectangleGraph a w h)
    (e : positiveActiveVertexSet (rectangleSubgraphDualGraph hK) ≃
      {v : LatticeVertex // v ∈ annulusVertexSet N})
    (hgraph : (positiveActiveGraph (rectangleSubgraphDualGraph hK)).map
        e.toEmbedding = annulusSourceGraph N) :
    Configuration (annulusSourceGraph N) ≃ Configuration K :=
  (Equiv.cast (congrArg Configuration hgraph.symm)).trans
    (positiveWiredSubgraphDualConfigurationEquiv hK e)

private theorem annulusLaw_eq_of_graph_eq
    {V : Type*} [Finite V] {G H : SimpleGraph V} (hGH : G = H)
    (θ : PottsContinuity.PD.FK.Parameters)
    (ξ : BoundaryCondition V) :
    (PottsContinuity.PD.FK.law G θ ξ).map
        (Equiv.cast (congrArg Configuration hGH)) =
      PottsContinuity.PD.FK.law H θ ξ := by
  cases hGH
  rw [Equiv.cast_refl]
  change (PottsContinuity.PD.FK.law G θ ξ).map id = _
  rw [PMF.map_id]

/-- Conditional exact law transfer for a separately wired annulus at any
admissible PD parameter record. The geometry premises identify the active
double dual with the annulus graph and its induced partition with the two
separate annulus classes. The dual law is free on the embedded dual annulus
graph at the dual parameter. -/
theorem annulus_separatelyWired_law_eq_embeddedDual_free_PD_of_doubleDualGeometry
    (N : ℕ) (hN : 1 ≤ N)
    {a : LatticeVertex} {w h : ℕ}
    {K : SimpleGraph (RectangleVertex a w h)}
    (hK : K ≤ rectangleGraph a w h)
    (e : positiveActiveVertexSet (rectangleSubgraphDualGraph hK) ≃
      {v : LatticeVertex // v ∈ annulusVertexSet N})
    (hgraph : (positiveActiveGraph (rectangleSubgraphDualGraph hK)).map
        e.toEmbedding = annulusSourceGraph N)
    (hpartition : (positiveWiredSubgraphDualBoundary hK e).partition =
      (annulusPrimalSeparatedBoundary N hN).partition)
    (θ : PottsContinuity.PD.FK.Parameters) :
    (PottsContinuity.PD.FK.law (annulusSourceGraph N)
      θ
      (annulusPrimalSeparatedBoundary N hN)).map
        (annulusPrimalToEmbeddedDualConfigurationEquiv N hK e hgraph) =
      PottsContinuity.PD.FK.law K
        (PottsContinuity.PD.Duality.dualParameters θ)
        (BoundaryCondition.free ∅) := by
  let A := positiveActiveGraph (rectangleSubgraphDualGraph hK)
  let ξ := positiveWiredSubgraphDualBoundary hK e
  let E := positiveWiredSubgraphDualConfigurationEquiv hK e
  have hcast := annulusLaw_eq_of_graph_eq hgraph.symm θ
    (annulusPrimalSeparatedBoundary N hN)
  have hrename := PottsContinuity.PD.FK.law_eq_of_boundary_partition_eq
    (G := A.map e.toEmbedding) θ
    (annulusPrimalSeparatedBoundary N hN)
    ξ hpartition.symm
  have hdual : (PottsContinuity.PD.FK.law
      (A.map e.toEmbedding) θ ξ).map E =
      PottsContinuity.PD.FK.law K
        (PottsContinuity.PD.Duality.dualParameters θ)
        (BoundaryCondition.free ∅) := by
    rw [← positiveFKLaw_eq_PD_law (θ := θ) (ξ := ξ)]
    rw [← positiveFKLaw_eq_PD_law (G := K)
      (θ := PottsContinuity.PD.Duality.dualParameters θ)
      (ξ := BoundaryCondition.free ∅)]
    simpa only [PottsContinuity.PD.Duality.dualParameters, edgeParameter] using
      positive_wired_subgraph_duality_law_induced_boundary hK
        (clusterWeight_pos θ) (edgeParameter_pos θ) (edgeParameter_lt_one θ) e
  calc
    _ = ((PottsContinuity.PD.FK.law (annulusSourceGraph N)
        θ (annulusPrimalSeparatedBoundary N hN)).map
          (Equiv.cast (congrArg Configuration hgraph.symm))).map E := by
            rw [PMF.map_comp]
            rfl
    _ = (PottsContinuity.PD.FK.law (A.map e.toEmbedding)
        θ (annulusPrimalSeparatedBoundary N hN)).map E := by
            simpa only [A] using congrArg (fun μ => μ.map E) hcast
    _ = (PottsContinuity.PD.FK.law (A.map e.toEmbedding)
        θ ξ).map E := by
            simpa only [A, ξ, E] using congrArg (fun μ => μ.map E) hrename
    _ = _ := by simpa only [A, E] using hdual

/-- Explicit self-dual specialization of the separately wired annulus law. The
dual carrier and its exact boundary partition remain the geometry premises. -/
theorem annulus_separatelyWired_law_eq_embeddedDual_free_at_selfDualParameter_of_doubleDualGeometry
    (N : ℕ) (hN : 1 ≤ N)
    {a : LatticeVertex} {w h : ℕ}
    {K : SimpleGraph (RectangleVertex a w h)}
    (hK : K ≤ rectangleGraph a w h)
    (e : positiveActiveVertexSet (rectangleSubgraphDualGraph hK) ≃
      {v : LatticeVertex // v ∈ annulusVertexSet N})
    (hgraph : (positiveActiveGraph (rectangleSubgraphDualGraph hK)).map
        e.toEmbedding = annulusSourceGraph N)
    (hpartition : (positiveWiredSubgraphDualBoundary hK e).partition =
      (annulusPrimalSeparatedBoundary N hN).partition)
    (q : Set.Ici (1 : ℝ)) :
    (PottsContinuity.PD.FK.law (annulusSourceGraph N)
      (PottsContinuity.PD.FK.criticalParameters q)
      (annulusPrimalSeparatedBoundary N hN)).map
        (annulusPrimalToEmbeddedDualConfigurationEquiv N hK e hgraph) =
      PottsContinuity.PD.FK.law K
        (PottsContinuity.PD.FK.criticalParameters q)
        (BoundaryCondition.free ∅) := by
  simpa only [PottsContinuity.PD.FK.dualParameters_criticalParameters]
    using annulus_separatelyWired_law_eq_embeddedDual_free_PD_of_doubleDualGeometry
      N hN hK e hgraph hpartition
      (PottsContinuity.PD.FK.criticalParameters q)

end
end PottsContinuity.DualityExt
