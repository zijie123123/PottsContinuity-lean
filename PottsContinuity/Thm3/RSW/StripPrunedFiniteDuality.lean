module

public import PottsContinuity.Thm3.RSW.StripWindowRectangleIso
public import PottsContinuity.Thm3.RSW.PrewiredSubgraphMarginal
public import PottsContinuity.DualityExt.PositiveInducedSourceBoundaryLaw
public import PottsContinuity.PD.FK.BoundaryPartitionLaw
public import PottsContinuity.Thm3.RSW.SelfDualSetup

@[expose] public section

namespace PottsContinuity.RSW
open PD.FK PD.Duality DualityExt
noncomputable section
local instance stripPrunedDualEdgeEq {V : Type*} (G : SimpleGraph V) :
    DecidableEq G.edgeSet := Classical.decEq _

/-- Deleting an actual specified edge set removes precisely that edge set. -/
theorem subgraphRemovedEdges_edgeRestriction {V : Type*} [Finite V]
    (G : SimpleGraph V) (R : Configuration G) :
    subgraphRemovedEdges (edgeRestriction G R) G=R := by
  classical
  ext e
  simp only [mem_subgraphRemovedEdges,edgeRestriction_edgeSet,Set.mem_sdiff,
    e.property,true_and,not_not,coe_mem_openEdges_iff]

/-- The original top-row bonds on the unchanged physical rectangle host. -/
def stripRectangleTopRowState (n M : ℕ) :
    Configuration (rectangleGraph (-(M:ℤ),-(n:ℤ)) (2*M) (4*n)) :=
  configurationIso (stripWindowRectangleIso n M) (stripTopRowState n M)

/-- Only the already wired original top-row bonds are omitted from sampling. -/
def stripRectangleWithoutTopGraph (n M : ℕ) :=
  edgeRestriction (rectangleGraph (-(M:ℤ),-(n:ℤ)) (2*M) (4*n)) (stripRectangleTopRowState n M)

section
variable (n M : ℕ)
local notation "Frame" => rectangleGraph (-(M:ℤ),-(n:ℤ)) (2*M) (4*n)
local notation "Point" => RectangleVertex (-(M:ℤ),-(n:ℤ)) (2*M) (4*n)
local notation "J" => stripRectangleWithoutTopGraph n M
local notation "R" => stripRectangleTopRowState n M
local notation "f" => Function.Embedding.refl Point
local notation "ξ" => boundaryConditionIso (stripWindowRectangleIso n M) (stripWindowBoundary n M 0)

private theorem pruned_map_id : (J).map f=J := by
  ext u v
  simp only [SimpleGraph.map_adj,Function.Embedding.refl_apply]
  constructor
  · rintro ⟨x,y,hxy,rfl,rfl⟩
    exact hxy
  · intro h
    exact ⟨u,v,h,rfl,rfl⟩

/-- The source top-deleted graph retains only original host bonds. -/
theorem stripRectangleWithoutTop_le : J ≤ Frame := edgeRestriction_le Frame R

/-- The omitted original bonds are exactly the source top row. -/
theorem stripRectangleWithoutTop_removedEdges : subgraphRemovedEdges J Frame=R := by
  change subgraphRemovedEdges (edgeRestriction Frame R) Frame=R
  exact subgraphRemovedEdges_edgeRestriction Frame R

/-- The complete physical top-deleted source graph embeds in its host. -/
theorem stripRectangleWithoutTop_map_le : (J).map f ≤ Frame := by
  rw [pruned_map_id]
  exact stripRectangleWithoutTop_le n M

/-- The host's fixed removed state opens exactly the original top row. -/
def stripRectangleTopRemovedState : RemovedConfiguration Frame
    (subgraphRemovedEdges ((J).map f) Frame) :=
  ⟨R,by
    rw [pruned_map_id]
    change R ⊆ subgraphRemovedEdges (edgeRestriction Frame R) Frame
    rw [subgraphRemovedEdges_edgeRestriction]⟩

/-- The source top-only arc is exactly induced by that fixed original state. -/
theorem stripRectangleTopRemovedState_source_partition :
    (ξ).partition = (isolatedExtensionPullbackBoundary f
      (frozenBoundary (BoundaryCondition.free ∅) (stripRectangleTopRemovedState n M).val)).partition := by
  change (ξ).partition=(frozenBoundary (BoundaryCondition.free ∅) R).partition
  exact (stripWindowRectangleIso_topRow_frozen_partition n M).symm

/-- The literal complementary dual equivalence for the actual pruned source. -/
def stripPrunedDualConfigurationEquiv : Configuration J ≃
    Configuration (rectangleSubgraphDualGraph (stripRectangleWithoutTop_map_le n M)) :=
  (isolatedExtensionConfigurationEquiv J f).trans
    (rectangleSubgraphDualConfigurationEquiv (stripRectangleWithoutTop_map_le n M))

/-- Read only the non-top source bonds, then their actual complementary duals. -/
def stripWindowPrunedDualConfiguration
    (C : Configuration (squareLattice.induce (stripWindow n M : Set (ℤ×ℤ)))) :=
  stripPrunedDualConfigurationEquiv n M
    (subgraphConfigurationRestriction (stripRectangleWithoutTop_le n M)
      (configurationIso (stripWindowRectangleIso n M) C))

/-- Exact finite dual law for the top-wired source strip after forgetting its
prewired top-row bonds. The target keeps the full actual host dual carrier and
the boundary induced by the literal removed state; no partition premise remains. -/
theorem stripWindowPrunedDualConfiguration_law (θ : Parameters) :
    (law (squareLattice.induce (stripWindow n M : Set (ℤ×ℤ))) θ (stripWindowBoundary n M 0)).map
      (stripWindowPrunedDualConfiguration n M) =
    law (rectangleSubgraphDualGraph (stripRectangleWithoutTop_map_le n M)) (dualParameters θ)
      (embeddedSubgraphInducedDualBoundary f (stripRectangleWithoutTop_map_le n M)
        (stripRectangleTopRemovedState n M)) := by
  have hiso := law_configurationIso_map θ (stripWindowRectangleIso n M) (stripWindowBoundary n M 0)
  have hr := law_map_subgraphRestriction_of_prewired (stripRectangleWithoutTop_le n M) θ ξ (by
    intro u v huv he
    rw [stripRectangleWithoutTop_removedEdges] at he
    have hpart : (frozenBoundary (BoundaryCondition.free ∅) R).partition=(ξ).partition :=
      stripWindowRectangleIso_topRow_frozen_partition n M
    rw [← hpart]
    change (componentSetoid Frame (BoundaryCondition.free ∅) R).r u v
    apply actualConnected_component
    apply actualConnected_of_adj
    rw [openGraph_adj]
    exact ⟨⟨s(u,v),(Frame).mem_edgeSet.mpr huv⟩,he,rfl⟩)
  have hd := positive_embedded_subgraph_induced_duality_law_PD_of_sourcePartition
    f (stripRectangleWithoutTop_map_le n M) θ ξ (stripRectangleTopRemovedState n M)
      (stripRectangleTopRemovedState_source_partition n M)
  calc
    _ = (((law (squareLattice.induce (stripWindow n M : Set (ℤ×ℤ))) θ
        (stripWindowBoundary n M 0)).map (configurationIso (stripWindowRectangleIso n M))).map
        (subgraphConfigurationRestriction (stripRectangleWithoutTop_le n M))).map
          (stripPrunedDualConfigurationEquiv n M) := by
      rw [PMF.map_comp,PMF.map_comp]
      rfl
    _ = (law J θ ξ).map (stripPrunedDualConfigurationEquiv n M) := by rw [hiso,hr]
    _ = _ := hd

/-- All removed primal top-row bonds are open, so their complementary
removed dual state is literally empty. -/
theorem stripRectangleTopRemovedState_dual_open_eq_empty :
    (rectangleSubgraphDualOpenRemovedState (stripRectangleWithoutTop_map_le n M)
      (stripRectangleTopRemovedState n M)).val=∅ := by
  change (subgraphRemovedEdges ((J).map f) Frame).map
      (rectangleDualEdgeEquiv (-(M:ℤ),-(n:ℤ)) (2*M) (4*n)).toEmbedding \
    (R).map (rectangleDualEdgeEquiv (-(M:ℤ),-(n:ℤ)) (2*M) (4*n)).toEmbedding=∅
  rw [pruned_map_id,stripRectangleWithoutTop_removedEdges,Finset.sdiff_self]

/-- The exact induced dual partition is the host exterior wiring. Top ports
are still part of this carrier; their incident top spokes have been deleted. -/
theorem stripRectangleTopRemovedState_dual_partition :
    (embeddedSubgraphInducedDualBoundary f (stripRectangleWithoutTop_map_le n M)
      (stripRectangleTopRemovedState n M)).partition =
      (rectangleDualBoundaryCondition (-(M:ℤ),-(n:ℤ)) (2*M) (4*n)).partition := by
  unfold embeddedSubgraphInducedDualBoundary
  rw [stripRectangleTopRemovedState_dual_open_eq_empty]
  exact componentSetoid_empty _ _

/-- Exact finite source mixed dual law on the actual top-spoke-deleted dual
carrier, with the target exterior partition explicitly identified. -/
theorem stripWindowPrunedDualConfiguration_law_wired (θ : Parameters) :
    (law (squareLattice.induce (stripWindow n M : Set (ℤ×ℤ))) θ (stripWindowBoundary n M 0)).map
      (stripWindowPrunedDualConfiguration n M) =
    law (rectangleSubgraphDualGraph (stripRectangleWithoutTop_map_le n M)) (dualParameters θ)
      (rectangleDualBoundaryCondition (-(M:ℤ),-(n:ℤ)) (2*M) (4*n)) := by
  rw [stripWindowPrunedDualConfiguration_law]
  apply law_eq_of_boundary_partition_eq
  exact stripRectangleTopRemovedState_dual_partition n M

/-- The actual finite mixed source dual law at the explicit self-dual value,
for every real q>=1 and every original finite strip window. -/
theorem selfDual_stripWindowPrunedDualConfiguration_law (q : Set.Ici (1:ℝ)) :
    (law (squareLattice.induce (stripWindow n M : Set (ℤ×ℤ))) (selfDualParameters q)
      (stripWindowBoundary n M 0)).map (stripWindowPrunedDualConfiguration n M) =
    law (rectangleSubgraphDualGraph (stripRectangleWithoutTop_map_le n M)) (selfDualParameters q)
      (rectangleDualBoundaryCondition (-(M:ℤ),-(n:ℤ)) (2*M) (4*n)) := by
  simpa only [selfDualParameters_fixed] using
    stripWindowPrunedDualConfiguration_law_wired n M (selfDualParameters q)

end
end
end PottsContinuity.RSW
